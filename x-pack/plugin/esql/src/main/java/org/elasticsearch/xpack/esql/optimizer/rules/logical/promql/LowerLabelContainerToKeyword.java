/*
 * Copyright Elasticsearch B.V. and/or licensed to Elasticsearch B.V. under one
 * or more contributor license agreements. Licensed under the Elastic License
 * 2.0; you may not use this file except in compliance with the Elastic License
 * 2.0.
 */

package org.elasticsearch.xpack.esql.optimizer.rules.logical.promql;

import org.elasticsearch.common.lucene.BytesRefs;
import org.elasticsearch.xpack.esql.VerificationException;
import org.elasticsearch.xpack.esql.analysis.AnalyzerContext;
import org.elasticsearch.xpack.esql.common.Failure;
import org.elasticsearch.xpack.esql.core.expression.Alias;
import org.elasticsearch.xpack.esql.core.expression.Attribute;
import org.elasticsearch.xpack.esql.core.expression.Expression;
import org.elasticsearch.xpack.esql.core.expression.Literal;
import org.elasticsearch.xpack.esql.core.expression.NameId;
import org.elasticsearch.xpack.esql.core.expression.NamedExpression;
import org.elasticsearch.xpack.esql.core.type.DataType;
import org.elasticsearch.xpack.esql.expression.function.scalar.convert.ToString;
import org.elasticsearch.xpack.esql.expression.function.scalar.timeseries.AbstractTimeSeriesMetadataFunction;
import org.elasticsearch.xpack.esql.expression.function.scalar.timeseries.TimeSeriesMetadataFilter;
import org.elasticsearch.xpack.esql.expression.function.scalar.timeseries.ToTimeSeriesMetadata;
import org.elasticsearch.xpack.esql.plan.logical.Eval;
import org.elasticsearch.xpack.esql.plan.logical.LogicalPlan;
import org.elasticsearch.xpack.esql.plan.logical.PackDims;
import org.elasticsearch.xpack.esql.plan.logical.Project;
import org.elasticsearch.xpack.esql.plan.logical.TopNBy;
import org.elasticsearch.xpack.esql.plan.logical.UnionAll;
import org.elasticsearch.xpack.esql.plan.logical.promql.PromqlCommand;
import org.elasticsearch.xpack.esql.plan.logical.promql.PromqlLabels;
import org.elasticsearch.xpack.esql.plan.logical.promql.operator.VectorBinarySet;
import org.elasticsearch.xpack.esql.rule.ParameterizedRule;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Temporary compatibility for nodes before 9.7, which cannot read the typed label container: lowers it in a translated PromQL
 * plan to the keyword {@code _timeseries} whenever such a node participates ({@link PromqlCommand#usesLabelContainer}).
 * <p>
 * Translation and {@link PushDownPromqlLabels} produce one representation: the series read their label container as keyword
 * views of the source, cast to a typed label container above the collapse ({@link ToTimeSeriesMetadata}). The keyword form is that plan
 * without the casts: each view is the keyword column it was cast from, and the label container of a series without labels is
 * null. An {@code or} keeps one series per label set on its label container as a whole, {@code __name__} included, rather than
 * on the match key that leaves {@code __name__} out: the verifier admits on a keyword label container only the unions where the
 * two agree. A key that compares labels in slots of their own compares them in its label container too, rather than leaving
 * them out of it, as keyword vector matching always has. What has no keyword form fails: reading a label out of the label container,
 * or leaving labels out of it after the collapse ({@link AbstractTimeSeriesMetadataFunction}).
 * <p>
 * Remove the rule once every supported version reads the typed label container.
 */
public final class LowerLabelContainerToKeyword extends ParameterizedRule<LogicalPlan, LogicalPlan, AnalyzerContext> {

    @Override
    public LogicalPlan apply(LogicalPlan plan, AnalyzerContext context) {
        if (PromqlCommand.usesLabelContainer(context) || plan.anyMatch(LowerLabelContainerToKeyword::readsTyped) == false) {
            return plan;
        }
        return lower(plan);
    }

    /** {@code plan} over a keyword label container. */
    static LogicalPlan lower(LogicalPlan plan) {
        Lowering lowering = new Lowering();
        return lowering.lower(dropUnread(lowering.keyOnLabelContainer(matchOnLabelContainer(plan))));
    }

    /** Every {@code or} keeping its series apart by their label container, without a match key of its own. */
    private static LogicalPlan matchOnLabelContainer(LogicalPlan plan) {
        if (plan.anyMatch(
            node -> node instanceof UnionAll union && union.output().stream().anyMatch(LowerLabelContainerToKeyword::isMatchKey)
        ) == false) {
            return plan;
        }
        return plan.transformUp(node -> switch (node) {
            case TopNBy top when top.groupings().stream().anyMatch(g -> g instanceof Attribute key && isMatchKey(key)) -> {
                List<Expression> groupings = top.groupings()
                    .stream()
                    .map(grouping -> grouping instanceof Attribute key && isMatchKey(key) ? labelContainerOf(top.child()) : grouping)
                    .toList();
                yield new TopNBy(top.source(), top.child(), top.order(), top.limitPerGroup(), groupings);
            }
            case UnionAll union -> union.replaceSubPlansAndOutput(
                union.children(),
                union.output().stream().filter(column -> isMatchKey(column) == false).toList()
            );
            case Project project when project.projections().stream().anyMatch(LowerLabelContainerToKeyword::isMatchKey) -> project
                .withProjections(project.projections().stream().filter(projection -> isMatchKey(projection) == false).toList());
            default -> node;
        });
    }

    private static Attribute labelContainerOf(LogicalPlan union) {
        return union.output()
            .stream()
            .filter(column -> isTyped(column) && isMatchKey(column) == false)
            .findFirst()
            .orElseThrow(() -> new IllegalStateException("an or with a match key holds the label container [" + union + "]"));
    }

    private static boolean isMatchKey(NamedExpression projection) {
        return projection.name().equals(VectorBinarySet.OR_MATCH_KEY);
    }

    /** {@code plan} without the typed label container it computes and never reads: such a column needs no keyword form. */
    private static LogicalPlan dropUnread(LogicalPlan plan) {
        while (true) {
            Map<NameId, Integer> reads = new HashMap<>();
            plan.forEachExpressionDown(Attribute.class, attribute -> reads.merge(attribute.id(), 1, Integer::sum));
            LogicalPlan pruned = plan.transformUp(Eval.class, eval -> {
                List<Alias> fields = eval.fields().stream().filter(field -> isRead(field, reads) || readsTyped(field) == false).toList();
                return fields.size() == eval.fields().size() ? eval
                    : fields.isEmpty() ? eval.child()
                    : new Eval(eval.source(), eval.child(), fields);
            });
            if (pruned == plan) {
                return plan;
            }
            plan = pruned;
        }
    }

    /** Whether something other than {@code field} itself reads it: a binding may reuse the id of the column it renames. */
    private static boolean isRead(Alias field, Map<NameId, Integer> reads) {
        int own = field.child().collect(Attribute.class).stream().mapToInt(attribute -> attribute.id().equals(field.id()) ? 1 : 0).sum();
        return reads.getOrDefault(field.id(), 0) > own;
    }

    private static boolean readsTyped(Expression expression) {
        return expression.anyMatch(LowerLabelContainerToKeyword::isTyped);
    }

    private static boolean readsTyped(LogicalPlan node) {
        return node.expressions().stream().anyMatch(LowerLabelContainerToKeyword::readsTyped);
    }

    private static boolean isTyped(Expression expression) {
        return expression.resolved() && expression.dataType() == DataType.TSMD_DATA_TYPE;
    }

    /**
     * A cast of a keyword label container to typed, or the rendering of a typed label container as keyword: both are the keyword column.
     */
    private static boolean isCast(Expression expression) {
        return (expression instanceof ToTimeSeriesMetadata cast && cast.field() instanceof Literal == false)
            || (expression instanceof ToString render && isTyped(render.field()));
    }

    /** One bottom-up pass; each node reads the columns of its input as they were lowered. */
    private static final class Lowering {
        /** Each column of a lowered node, by id. */
        private final Map<NameId, Attribute> lowered = new HashMap<>();
        /** The keyword column each dropped cast stood for, by the cast's id. */
        private final Map<NameId, Attribute> casts = new HashMap<>();
        /** Label container keys that keep every label they left out, by id: each is the label container it was derived from. */
        private final Set<NameId> keptWhole = new HashSet<>();
        /** Projections left bare by dropping the casts over them: a projection above only reorders their columns. */
        private final Set<LogicalPlan> bare = Collections.newSetFromMap(new IdentityHashMap<>());

        /**
         * {@code plan} with each packed key's label container keeping the labels the key compares in slots of their own: keyword
         * label container cannot leave them out, and comparing them twice keeps the key it always had.
         */
        LogicalPlan keyOnLabelContainer(LogicalPlan plan) {
            Map<NameId, Set<String>> slotted = new HashMap<>();
            plan.forEachDown(PackDims.class, pack -> {
                Set<String> labels = new HashSet<>();
                for (Attribute dim : pack.dims()) {
                    if (isTyped(dim) == false) {
                        labels.add(PromqlLabels.labelName(dim));
                    }
                }
                for (Attribute dim : pack.dims()) {
                    if (isTyped(dim)) {
                        slotted.computeIfAbsent(dim.id(), id -> new HashSet<>()).addAll(labels);
                    }
                }
            });
            if (slotted.isEmpty()) {
                return plan;
            }
            return plan.transformUp(Eval.class, eval -> {
                List<Alias> fields = eval.fields().stream().map(field -> {
                    if (slotted.containsKey(field.id()) && field.child() instanceof TimeSeriesMetadataFilter unset && unset.exclude()) {
                        List<Expression> left = unset.children()
                            .subList(1, unset.children().size())
                            .stream()
                            .filter(label -> slotted.get(field.id()).contains(BytesRefs.toString(((Literal) label).value())) == false)
                            .toList();
                        if (left.isEmpty()) {
                            keptWhole.add(field.id());
                            return field.replaceChild(unset.labelContainer());
                        }
                        return field.replaceChild(new TimeSeriesMetadataFilter(unset.source(), unset.labelContainer(), left, true));
                    }
                    return field;
                }).toList();
                return fields.equals(eval.fields()) ? eval : new Eval(eval.source(), eval.child(), fields);
            });
        }

        LogicalPlan lower(LogicalPlan plan) {
            return plan.transformUp(node -> {
                LogicalPlan rewritten = switch (node) {
                    case Eval eval -> withoutCasts(eval);
                    case Project project -> project.withProjections(project.projections().stream().map(this::withoutCast).toList());
                    default -> node;
                };
                rewritten = rewritten.transformExpressionsOnly(Expression.class, this::lower);
                if (rewritten instanceof Project outer && bare.contains(outer.child())) {
                    rewritten = reorder(outer, (Project) outer.child());
                }
                rewritten.output().forEach(attribute -> lowered.put(attribute.id(), attribute));
                return rewritten;
            });
        }

        /** {@code eval} without the fields that only cast: their readers read the keyword column. */
        private LogicalPlan withoutCasts(Eval eval) {
            var fields = new ArrayList<Alias>();
            for (Alias field : eval.fields()) {
                if (isCast(field.child()) || keptWhole.contains(field.id())) {
                    casts.put(field.id(), (Attribute) lower(field.child()));
                } else {
                    fields.add(field);
                }
            }
            if (fields.isEmpty() && eval.child() instanceof Project projection) {
                bare.add(projection);
            }
            return fields.size() == eval.fields().size() ? eval
                : fields.isEmpty() ? eval.child()
                : new Eval(eval.source(), eval.child(), fields);
        }

        /** {@code inner} in the order {@code outer} projects its columns. */
        private static Project reorder(Project outer, Project inner) {
            Map<NameId, NamedExpression> byId = new HashMap<>();
            inner.projections().forEach(projection -> byId.put(projection.id(), projection));
            var projections = new ArrayList<NamedExpression>(outer.projections().size());
            for (NamedExpression projection : outer.projections()) {
                NamedExpression column = byId.get(projection.id());
                if (column == null || projection instanceof Attribute == false) {
                    return outer;
                }
                projections.add(column);
            }
            return new Project(outer.source(), inner.child(), projections);
        }

        private NamedExpression withoutCast(NamedExpression projection) {
            if (projection instanceof Alias alias && isCast(alias.child())) {
                Attribute column = (Attribute) lower(alias.child());
                casts.put(alias.id(), column);
                return column;
            }
            return projection;
        }

        /** {@code expression} over a keyword label container. Top-down: a cast is gone before its operand is looked at. */
        private Expression lower(Expression expression) {
            return switch (expression) {
                case ToTimeSeriesMetadata cast when cast.field() instanceof Literal -> new Literal(cast.source(), null, DataType.KEYWORD);
                case ToTimeSeriesMetadata cast -> lower(cast.field());
                case ToString render when isTyped(render.field()) -> lower(render.field());
                case AbstractTimeSeriesMetadataFunction function -> throw new VerificationException(
                    List.of(
                        Failure.fail(
                            function,
                            "leaving labels out of _timeseries requires a typed label container [{}]",
                            function.sourceText()
                        )
                    )
                );
                case Attribute attribute when casts.containsKey(attribute.id()) -> casts.get(attribute.id());
                case Attribute attribute when isTyped(attribute) -> {
                    Attribute below = lowered.get(attribute.id());
                    yield below != null && isTyped(below) == false ? below : attribute.withDataType(DataType.KEYWORD);
                }
                default -> {
                    List<Expression> children = expression.children();
                    List<Expression> rewritten = children.stream().map(this::lower).toList();
                    yield rewritten.equals(children) ? expression : expression.replaceChildren(rewritten);
                }
            };
        }
    }
}
