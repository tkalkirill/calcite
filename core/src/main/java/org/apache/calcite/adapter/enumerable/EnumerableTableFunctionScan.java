/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.adapter.enumerable;

import org.apache.calcite.DataContext;
import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.linq4j.function.Function1;
import org.apache.calcite.linq4j.tree.BlockBuilder;
import org.apache.calcite.linq4j.tree.BlockStatement;
import org.apache.calcite.linq4j.tree.Expression;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.linq4j.tree.ParameterExpression;
import org.apache.calcite.linq4j.tree.Primitive;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.plan.RelOptUtil;
import org.apache.calcite.rel.core.CorrelationId;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.TableFunctionScan;
import org.apache.calcite.rel.metadata.RelColumnMapping;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.schema.ImplementableFunction;
import org.apache.calcite.schema.QueryableTable;
import org.apache.calcite.schema.impl.TableFunctionImpl;
import org.apache.calcite.sql.SqlWindowTableFunction;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.validate.SqlConformance;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.sql.validate.SqlUserDefinedFunction;
import org.apache.calcite.sql.validate.SqlUserDefinedTableFunction;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.util.BuiltInMethod;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/** Implementation of {@link org.apache.calcite.rel.core.TableFunctionScan} in
 * {@link org.apache.calcite.adapter.enumerable.EnumerableConvention enumerable calling convention}. */
public class EnumerableTableFunctionScan extends TableFunctionScan
    implements EnumerableRel {

  public EnumerableTableFunctionScan(RelOptCluster cluster,
      RelTraitSet traits, List<RelNode> inputs, @Nullable Type elementType,
      RelDataType rowType, RexNode call,
      @Nullable Set<RelColumnMapping> columnMappings) {
    super(cluster, traits, inputs, call, elementType, rowType,
        columnMappings);
  }

  @Override public EnumerableTableFunctionScan copy(
      RelTraitSet traitSet,
      List<RelNode> inputs,
      RexNode rexCall,
      @Nullable Type elementType,
      RelDataType rowType,
      @Nullable Set<RelColumnMapping> columnMappings) {
    return new EnumerableTableFunctionScan(getCluster(), traitSet, inputs,
        elementType, rowType, rexCall, columnMappings);
  }

  @Override public Result implement(EnumerableRelImplementor implementor, Prefer pref) {
    if (isScalarUserDefinedFunctionWithCursorInputs((RexCall) getCall())) {
      return scalarUserDefinedFunctionImplement(implementor, pref);
    } else if (isImplementorDefined((RexCall) getCall())) {
      return tvfImplementorBasedImplement(implementor, pref);
    } else {
      return defaultTableFunctionImplement(implementor, pref);
    }
  }

  private static boolean isImplementorDefined(RexCall call) {
    if (call.getOperator() instanceof SqlWindowTableFunction
        && RexImpTable.INSTANCE.get((SqlWindowTableFunction) call.getOperator()) != null) {
      return true;
    }
    return false;
  }

  private boolean isScalarUserDefinedFunctionWithCursorInputs(RexCall call) {
    return !getInputs().isEmpty()
        && containsScalarUserDefinedFunctionWithCursorInputs(call);
  }

  private Result scalarUserDefinedFunctionImplement(
      EnumerableRelImplementor implementor, Prefer pref) {
    if (hasOuterInput()) {
      return correlatedScalarUserDefinedFunctionImplement(implementor, pref);
    }
    return uncorrelatedScalarUserDefinedFunctionImplement(implementor, pref);
  }

  private Result uncorrelatedScalarUserDefinedFunctionImplement(
      EnumerableRelImplementor implementor, Prefer pref) {
    final JavaTypeFactory typeFactory = implementor.getTypeFactory();
    final BlockBuilder builder = new BlockBuilder();
    final PhysType physType =
        PhysTypeImpl.of(typeFactory, getRowType(), pref.prefer(JavaRowFormat.SCALAR));
    final RexCall call = (RexCall) getCall();
    final SqlConformance conformance =
        (SqlConformance) implementor.map.getOrDefault("_conformance",
            SqlConformanceEnum.DEFAULT);
    final List<RexToLixTranslator.Result> cursorResults = new ArrayList<>();
    for (int i = 0; i < getInputs().size(); i++) {
      final EnumerableRel child = (EnumerableRel) getInputs().get(i);
      final Result result =
          implementor.visitChild(this, i, child, Prefer.ARRAY);
      final Expression inputEnumerable =
          builder.append("cursor", result.block, false);
      final ParameterExpression inputEnumerableVariable =
          Expressions.parameter(inputEnumerable.getType(), "cursor" + i);
      builder.add(
          Expressions.declare(Modifier.FINAL, inputEnumerableVariable,
              inputEnumerable));
      cursorResults.add(
          new RexToLixTranslator.Result(null, inputEnumerableVariable));
    }
    final RexToLixTranslator translator =
        RexToLixTranslator.forAggregation(typeFactory, builder, null, conformance)
            .setCallResultProvider(
                (t, c) -> implementCursorUserDefinedFunction(t, c, cursorResults));
    final List<Expression> fieldExpressions =
        implementOutputExpressions(translator, call);
    final Expression row =
        physType.record(fieldExpressions);
    builder.add(
        Expressions.return_(null,
            Expressions.call(BuiltInMethod.SINGLETON_ENUMERABLE.method, row)));
    final BlockStatement block = builder.toBlock();
    return implementor.result(physType, block);
  }

  private Result correlatedScalarUserDefinedFunctionImplement(
      EnumerableRelImplementor implementor, Prefer pref) {
    final JavaTypeFactory typeFactory = implementor.getTypeFactory();
    final BlockBuilder builder = new BlockBuilder();
    final PhysType physType =
        PhysTypeImpl.of(typeFactory, getRowType(), pref.prefer(JavaRowFormat.SCALAR));
    final RexCall call = (RexCall) getCall();

    final EnumerableRel outer = (EnumerableRel) getInputs().get(0);
    final Result outerResult =
        implementor.visitChild(this, 0, outer, pref);
    final Expression outerEnumerable =
        builder.append("outer", outerResult.block, false);

    final BlockBuilder lambdaBuilder = new BlockBuilder();
    final Type outerJavaRowType = outerResult.physType.getJavaRowType();
    final ParameterExpression outerArg;
    final ParameterExpression outerRef;
    if (!Primitive.is(outerJavaRowType)) {
      outerArg =
          Expressions.parameter(Modifier.FINAL, outerJavaRowType, "outerRow");
      outerRef = outerArg;
    } else {
      outerArg =
          Expressions.parameter(Modifier.FINAL,
              Primitive.box(outerJavaRowType), "$boxOuterRow");
      outerRef =
          (ParameterExpression) lambdaBuilder.append("outerRow",
              Expressions.unbox(outerArg));
    }

    final List<CorrelationId> correlationIds = new ArrayList<>();
    for (RelNode input : getInputs().subList(1, getInputs().size())) {
      for (CorrelationId id : RelOptUtil.getVariablesUsed(input)) {
        if (!correlationIds.contains(id)) {
          correlationIds.add(id);
        }
      }
    }
    for (CorrelationId id : correlationIds) {
      implementor.registerCorrelVariable(id.getName(), outerRef, lambdaBuilder,
          outerResult.physType);
    }

    final List<RexToLixTranslator.Result> cursorResults = new ArrayList<>();
    for (int i = 1; i < getInputs().size(); i++) {
      final EnumerableRel child = (EnumerableRel) getInputs().get(i);
      final Result result =
          implementor.visitChild(this, i, child, Prefer.ARRAY);
      final Expression inputEnumerable =
          lambdaBuilder.append("cursor", result.block, false);
      final ParameterExpression inputEnumerableVariable =
          Expressions.parameter(inputEnumerable.getType(), "cursor" + (i - 1));
      lambdaBuilder.add(
          Expressions.declare(Modifier.FINAL, inputEnumerableVariable,
              inputEnumerable));
      cursorResults.add(
          new RexToLixTranslator.Result(null, inputEnumerableVariable));
    }

    for (CorrelationId id : correlationIds) {
      implementor.clearCorrelVariable(id.getName());
    }

    final SqlConformance conformance =
        (SqlConformance) implementor.map.getOrDefault("_conformance",
            SqlConformanceEnum.DEFAULT);
    final RexToLixTranslator translator =
        RexToLixTranslator.forAggregation(typeFactory, lambdaBuilder,
            new RexToLixTranslator.InputGetterImpl(outerRef, outerResult.physType),
            conformance)
            .setCallResultProvider(
                (t, c) -> implementCursorUserDefinedFunction(t, c, cursorResults));
    final List<Expression> fieldExpressions =
        implementOutputExpressions(translator, call);
    final Expression row =
        physType.record(fieldExpressions);
    lambdaBuilder.add(
        Expressions.return_(null,
            Expressions.call(BuiltInMethod.SINGLETON_ENUMERABLE.method, row)));

    builder.add(
        Expressions.return_(null,
            Expressions.call(outerEnumerable, BuiltInMethod.SELECT_MANY.method,
                Expressions.lambda(Function1.class, lambdaBuilder.toBlock(),
                    outerArg))));
    return implementor.result(physType, builder.toBlock());
  }

  private boolean hasOuterInput() {
    return getInputs().size() > cursorCount((RexCall) getCall());
  }

  private static int cursorCount(RexCall call) {
    int count = 0;
    for (RexNode operand : outputOperands(call)) {
      count = Math.max(count, maxCursorInputIndex(operand) + 1);
    }
    return count;
  }

  private static boolean containsScalarUserDefinedFunctionWithCursorInputs(
      RexNode node) {
    if (node instanceof RexCall) {
      final RexCall call = (RexCall) node;
      if (call.getOperator() instanceof SqlUserDefinedFunction
          && maxCursorInputIndex(call) >= 0) {
        return true;
      }
      for (RexNode operand : call.getOperands()) {
        if (containsScalarUserDefinedFunctionWithCursorInputs(operand)) {
          return true;
        }
      }
    }
    return false;
  }

  private static int maxCursorInputIndex(RexNode node) {
    final int cursorInputIndex = cursorInputIndex(node);
    if (cursorInputIndex >= 0) {
      return cursorInputIndex;
    }
    int max = -1;
    if (node instanceof RexCall) {
      for (RexNode operand : ((RexCall) node).getOperands()) {
        max = Math.max(max, maxCursorInputIndex(operand));
      }
    }
    return max;
  }

  private static List<RexNode> outputOperands(RexCall call) {
    if (call.getOperator() == SqlStdOperatorTable.ROW) {
      return call.getOperands();
    }
    return Collections.singletonList(call);
  }

  private static List<Expression> implementOutputExpressions(
      RexToLixTranslator translator, RexCall call) {
    final List<Expression> expressions = new ArrayList<>();
    for (RexNode operand : outputOperands(call)) {
      expressions.add(implementOutputExpression(translator, operand));
    }
    return expressions;
  }

  private static Expression implementOutputExpression(
      RexToLixTranslator translator, RexNode node) {
    return node.accept(translator).valueVariable;
  }

  private static RexToLixTranslator.@Nullable Result implementCursorUserDefinedFunction(
      RexToLixTranslator translator, RexCall call,
      List<RexToLixTranslator.Result> cursorResults) {
    if (!(call.getOperator() instanceof SqlUserDefinedFunction)
        || maxCursorInputIndex(call) < 0) {
      return null;
    }
    final Expression callExpression =
        implementScalarCall((SqlUserDefinedFunction) call.getOperator(),
            translator, call, cursorResults);
    final ParameterExpression value =
        Expressions.parameter(callExpression.getType(),
            translator.getBlockBuilder().newName("cursorUdf"));
    translator.getBlockBuilder().add(
        Expressions.declare(Modifier.FINAL, value, callExpression));
    final ParameterExpression isNull =
        Expressions.parameter(Boolean.TYPE,
            translator.getBlockBuilder().newName("cursorUdf_isNull"));
    translator.getBlockBuilder().add(
        Expressions.declare(Modifier.FINAL, isNull,
            translator.checkNull(value)));
    return new RexToLixTranslator.Result(isNull, value);
  }

  private static Expression implementScalarCall(SqlUserDefinedFunction udf,
      RexToLixTranslator translator, RexCall call,
      List<RexToLixTranslator.Result> cursorResults) {
    if (!(udf.getFunction() instanceof ImplementableFunction)) {
      throw new IllegalStateException("User defined function " + udf
          + " must implement ImplementableFunction");
    }
    final List<RexToLixTranslator.Result> operandResults = new ArrayList<>();
    for (RexNode operand : call.getOperands()) {
      final int cursorIndex = cursorInputIndex(operand);
      if (cursorIndex >= 0 && cursorIndex < cursorResults.size()) {
        operandResults.add(cursorResults.get(cursorIndex));
        continue;
      }
      operandResults.add(operand.accept(translator));
    }
    translator.setCallOperandResult(call, operandResults);
    return ((ImplementableFunction) udf.getFunction()).getImplementor()
        .implement(translator, call, RexImpTable.NullAs.NULL);
  }

  private static int cursorInputIndex(RexNode operand) {
    return cursorInputIndex(operand, false);
  }

  private static int cursorInputIndex(RexNode operand, boolean cursorContext) {
    if (operand instanceof RexInputRef
        && (cursorContext
            || operand.getType().getSqlTypeName() == SqlTypeName.CURSOR)) {
      return ((RexInputRef) operand).getIndex();
    }
    if (operand instanceof RexCall
        && operand.getType().getSqlTypeName() == SqlTypeName.CURSOR) {
      final List<RexNode> operands = ((RexCall) operand).getOperands();
      if (operands.size() == 1) {
        return cursorInputIndex(operands.get(0), true);
      }
    }
    return -1;
  }

  private boolean isQueryable() {
    if (!(getCall() instanceof RexCall)) {
      return false;
    }
    final RexCall call = (RexCall) getCall();
    if (!(call.getOperator() instanceof SqlUserDefinedTableFunction)) {
      return false;
    }
    final SqlUserDefinedTableFunction udtf =
        (SqlUserDefinedTableFunction) call.getOperator();
    if (!(udtf.getFunction() instanceof TableFunctionImpl)) {
      return false;
    }
    final TableFunctionImpl tableFunction =
        (TableFunctionImpl) udtf.getFunction();
    final Method method = tableFunction.method;
    return QueryableTable.class.isAssignableFrom(method.getReturnType());
  }

  private Result defaultTableFunctionImplement(
      EnumerableRelImplementor implementor,
      @SuppressWarnings("unused") Prefer pref) { // TODO: remove or use
    BlockBuilder bb = new BlockBuilder();
    // Non-array user-specified types are not supported yet
    final JavaRowFormat format;
    Type elementType = getElementType();
    if (elementType == null) {
      format = JavaRowFormat.ARRAY;
    } else if (getRowType().getFieldCount() == 1 && isQueryable()) {
      format = JavaRowFormat.SCALAR;
    } else if (elementType instanceof Class
        && Object[].class.isAssignableFrom((Class<?>) elementType)) {
      format = JavaRowFormat.ARRAY;
    } else {
      format = JavaRowFormat.CUSTOM;
    }
    final PhysType physType =
        PhysTypeImpl.of(implementor.getTypeFactory(), getRowType(), format,
            false);
    RexToLixTranslator t =
        RexToLixTranslator.forAggregation(
            (JavaTypeFactory) getCluster().getTypeFactory(),
            bb, null, implementor.getConformance());
    t = t.setCorrelates(implementor.allCorrelateVariables);
    bb.add(Expressions.return_(null, t.translate(getCall())));
    return implementor.result(physType, bb.toBlock());
  }

  private Result tvfImplementorBasedImplement(
      EnumerableRelImplementor implementor, Prefer pref) {
    final JavaTypeFactory typeFactory = implementor.getTypeFactory();
    final BlockBuilder builder = new BlockBuilder();
    final EnumerableRel child = (EnumerableRel) getInputs().get(0);
    final Result result =
        implementor.visitChild(this, 0, child, pref);
    final PhysType physType =
        PhysTypeImpl.of(typeFactory, getRowType(), pref.prefer(result.format));
    final Expression inputEnumerable =
        builder.append("_input", result.block, false);
    final SqlConformance conformance =
        (SqlConformance) implementor.map.getOrDefault("_conformance",
            SqlConformanceEnum.DEFAULT);

    builder.add(
        RexToLixTranslator.translateTableFunction(
            typeFactory,
            conformance,
            builder,
            DataContext.ROOT,
            (RexCall) getCall(),
            inputEnumerable,
            result.physType,
            physType));

    return implementor.result(physType, builder.toBlock());
  }
}
