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
import org.apache.calcite.adapter.enumerable.RexImpTable.RexCallImplementor;
import org.apache.calcite.adapter.java.JavaTypeFactory;
import org.apache.calcite.linq4j.Enumerable;
import org.apache.calcite.linq4j.tree.BlockBuilder;
import org.apache.calcite.linq4j.tree.Expression;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.linq4j.tree.ParameterExpression;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.TableFunctionScan;
import org.apache.calcite.rel.metadata.RelColumnMapping;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexInputRef;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.schema.QueryableTable;
import org.apache.calcite.schema.impl.TableFunctionImpl;
import org.apache.calcite.sql.SqlTableFunction;
import org.apache.calcite.sql.SqlWindowTableFunction;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql.util.CursorInput;
import org.apache.calcite.sql.util.CursorInputs;
import org.apache.calcite.sql.validate.SqlUserDefinedTableFunction;

import org.checkerframework.checker.nullness.qual.Nullable;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.ArrayList;
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
    if (isImplementorDefined((RexCall) getCall())) {
      return tvfImplementorBasedImplement(implementor, pref);
    } else if (isTableFunctionWithCursorInputs(implementor)) {
      return cursorTableFunctionImplement(implementor);
    } else {
      return defaultTableFunctionImplement(implementor);
    }
  }

  private static boolean isImplementorDefined(RexCall call) {
    if (call.getOperator() instanceof SqlWindowTableFunction
        && RexImpTable.INSTANCE.get((SqlWindowTableFunction) call.getOperator()) != null) {
      return true;
    }
    return false;
  }

  private boolean isTableFunctionWithCursorInputs(
      EnumerableRelImplementor implementor) {
    if (getInputs().isEmpty()
        || !(getCall() instanceof RexCall)) {
      return false;
    }
    final RexCall call = (RexCall) getCall();
    if (rexCallImplementor(implementor, call) == null) {
      return false;
    }
    for (RexNode operand : call.getOperands()) {
      if (cursorInputIndex(operand) >= 0) {
        return true;
      }
    }
    return false;
  }

  private Result cursorTableFunctionImplement(
      EnumerableRelImplementor implementor) {
    final JavaTypeFactory typeFactory = implementor.getTypeFactory();
    final BlockBuilder builder = new BlockBuilder();
    final PhysType physType = createPhysType(implementor);
    final List<RexToLixTranslator.Result> cursorResults = new ArrayList<>();

    for (int i = 0; i < getInputs().size(); i++) {
      final EnumerableRel child = (EnumerableRel) getInputs().get(i);
      final Result result = implementor.visitChild(this, i, child, Prefer.ARRAY);
      final Expression rows = builder.append("cursorRows", result.block, false);
      final Expression arrayRows =
          result.physType.convertTo(rows, JavaRowFormat.ARRAY);
      final Expression rowType =
          implementor.stash(getInputs().get(i).getRowType(), RelDataType.class);
      final Expression cursor =
          Expressions.call(CursorInputs.class, "of", rowType,
              Expressions.convert_(arrayRows, Enumerable.class));
      final ParameterExpression cursorVariable =
          Expressions.parameter(CursorInput.class,
              builder.newName("cursorInput"));
      builder.add(
          Expressions.declare(Modifier.FINAL, cursorVariable, cursor));
      final ParameterExpression isNull =
          Expressions.parameter(boolean.class,
              builder.newName("cursorInput_isNull"));
      builder.add(
          Expressions.declare(Modifier.FINAL, isNull,
              Expressions.constant(false)));
      cursorResults.add(new RexToLixTranslator.Result(isNull, cursorVariable));
    }

    final RexToLixTranslator translator =
        RexToLixTranslator.forAggregation(typeFactory, builder, null,
            implementor.getConformance(), implementor.getRexImplementorTable())
            .setCorrelates(implementor.allCorrelateVariables);
    final RexCall call = (RexCall) getCall();
    final List<RexToLixTranslator.Result> operandResults = new ArrayList<>();
    for (RexNode operand : call.getOperands()) {
      final int cursorIndex = cursorInputIndex(operand);
      operandResults.add(cursorIndex >= 0
          ? cursorResults.get(cursorIndex)
          : operand.accept(translator));
    }
    translator.setCallOperandResult(call, operandResults);
    final RexCallImplementor rexCallImplementor =
        rexCallImplementor(implementor, call);
    if (rexCallImplementor == null) {
      throw new IllegalStateException("Table function " + call.getOperator()
          + " has no implementation");
    }
    final RexToLixTranslator.Result result =
        rexCallImplementor.implement(translator, call, operandResults);
    final Expression enumerable =
        RexImpTable.NullAs.NULL.handle(result.valueVariable);
    builder.add(Expressions.return_(null, enumerable));
    return implementor.result(physType, builder.toBlock());
  }

  private static @Nullable RexCallImplementor rexCallImplementor(
      EnumerableRelImplementor implementor, RexCall call) {
    if (!(call.getOperator() instanceof SqlTableFunction)) {
      return null;
    }
    return implementor.getRexImplementorTable().get(call.getOperator());
  }

  private static int cursorInputIndex(RexNode node) {
    return cursorInputIndex(node, false);
  }

  private static int cursorInputIndex(RexNode node, boolean cursorContext) {
    if (node instanceof RexInputRef
        && (cursorContext
            || node.getType().getSqlTypeName() == SqlTypeName.CURSOR)) {
      return ((RexInputRef) node).getIndex();
    }
    if (node instanceof RexCall
        && node.getType().getSqlTypeName() == SqlTypeName.CURSOR) {
      final List<RexNode> operands = ((RexCall) node).getOperands();
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
      EnumerableRelImplementor implementor) {
    BlockBuilder bb = new BlockBuilder();
    final PhysType physType = createPhysType(implementor);
    RexToLixTranslator t =
        RexToLixTranslator.forAggregation(
            (JavaTypeFactory) getCluster().getTypeFactory(),
            bb, null, implementor.getConformance());
    t = t.setCorrelates(implementor.allCorrelateVariables);
    bb.add(Expressions.return_(null, t.translate(getCall())));
    return implementor.result(physType, bb.toBlock());
  }

  private PhysType createPhysType(EnumerableRelImplementor implementor) {
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
    return physType;
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
    builder.add(
        RexToLixTranslator.translateTableFunction(
            typeFactory,
            implementor.getConformance(),
            builder,
            DataContext.ROOT,
            (RexCall) getCall(),
            inputEnumerable,
            result.physType,
            physType));

    return implementor.result(physType, builder.toBlock());
  }
}
