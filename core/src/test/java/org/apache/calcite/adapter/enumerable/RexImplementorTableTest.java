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
import org.apache.calcite.jdbc.JavaTypeFactoryImpl;
import org.apache.calcite.linq4j.Enumerable;
import org.apache.calcite.linq4j.Linq4j;
import org.apache.calcite.linq4j.QueryProvider;
import org.apache.calcite.linq4j.tree.BlockBuilder;
import org.apache.calcite.linq4j.tree.Expression;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.plan.ConventionTraitDef;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.volcano.VolcanoPlanner;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeSystem;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexCall;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.rex.RexProgram;
import org.apache.calcite.rex.RexProgramBuilder;
import org.apache.calcite.runtime.Bindable;
import org.apache.calcite.schema.SchemaPlus;
import org.apache.calcite.sql.SqlAggFunction;
import org.apache.calcite.sql.SqlFunction;
import org.apache.calcite.sql.SqlFunctionCategory;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.SqlMatchFunction;
import org.apache.calcite.sql.SqlOperator;
import org.apache.calcite.sql.SqlWindowTableFunction;
import org.apache.calcite.sql.fun.SqlBasicAggFunction;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.OperandTypes;
import org.apache.calcite.sql.type.ReturnTypes;
import org.apache.calcite.sql.type.SqlTypeName;
import org.apache.calcite.sql.validate.SqlConformanceEnum;
import org.apache.calcite.test.MockSqlOperatorTable;

import com.google.common.collect.ImmutableList;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Type;
import java.math.BigDecimal;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.CoreMatchers.notNullValue;
import static org.hamcrest.CoreMatchers.nullValue;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.Matchers.hasSize;
import static org.hamcrest.Matchers.sameInstance;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Tests for the {@link RexImplementorTable} SPI, its
 * {@link RexImplementorTables#chain composition}, and its use by
 * {@link RexToLixTranslator}.
 */
class RexImplementorTableTest {
  /** A scalar operator that has no built-in implementor. */
  private static final SqlOperator MY_FN =
      new SqlFunction("MY_CUSTOM_FN", SqlKind.OTHER_FUNCTION,
          ReturnTypes.BOOLEAN, null, OperandTypes.ANY,
          SqlFunctionCategory.USER_DEFINED_FUNCTION);

  /** A sentinel implementor; only its identity matters to these tests. */
  private static final RexCallImplementor SENTINEL =
      (translator, call, arguments) -> {
        throw new UnsupportedOperationException("sentinel");
      };

  /** A sentinel aggregate implementor; only its identity matters. */
  private static final AggImplementor AGG_SENTINEL = new AggImplementor() {
    @Override public List<Type> getStateType(AggContext info) {
      throw new UnsupportedOperationException();
    }

    @Override public void implementReset(AggContext info, AggResetContext reset) {
      throw new UnsupportedOperationException();
    }

    @Override public void implementAdd(AggContext info, AggAddContext add) {
      throw new UnsupportedOperationException();
    }

    @Override public Expression implementResult(AggContext info,
        AggResultContext result) {
      throw new UnsupportedOperationException();
    }
  };

  /** An aggregate function with no built-in implementor. */
  private static final SqlAggFunction MY_AGG =
      SqlBasicAggFunction.create("MY_CUSTOM_AGG", SqlKind.OTHER_FUNCTION,
          ReturnTypes.BIGINT, OperandTypes.ANY);

  /** Implementor table that knows a single scalar operator. */
  private static final class SingleScalarTable implements RexImplementorTable {
    private final SqlOperator operator;
    private final RexCallImplementor implementor;

    SingleScalarTable(SqlOperator operator, RexCallImplementor implementor) {
      this.operator = operator;
      this.implementor = implementor;
    }

    @Override public @Nullable RexCallImplementor get(SqlOperator op) {
      return op == operator ? implementor : null;
    }

    @Override public @Nullable AggImplementor get(SqlAggFunction aggregation,
        boolean forWindowAggregate) {
      return null;
    }

    @Override public @Nullable MatchImplementor get(SqlMatchFunction function) {
      return null;
    }

    @Override public @Nullable TableFunctionCallImplementor get(
        SqlWindowTableFunction operator) {
      return null;
    }
  }

  /** The built-in table has no implementor for an unregistered operator. */
  @Test void builtinHasNoImplementorForUnknownOperator() {
    assertThat(RexImpTable.instance().get(MY_FN), is(nullValue()));
  }

  /** A chained extension table supplies the implementor for its own operator,
   * while the built-in table still resolves standard operators. */
  @Test void chainResolvesExtensionThenFallsBackToBuiltin() {
    final RexImplementorTable chain =
        RexImplementorTables.chain(new SingleScalarTable(MY_FN, SENTINEL),
            RexImpTable.instance());
    assertThat(chain.get(MY_FN), is(sameInstance(SENTINEL)));
    assertThat(chain.get(SqlStdOperatorTable.UPPER), is(notNullValue()));
  }

  /** Executes a table function with a cursor using an implementor supplied by
   * an extension table. */
  @Test void executesTableFunctionWithCursorFromExtensionTable() {
    final JavaTypeFactoryImpl typeFactory =
        new JavaTypeFactoryImpl(RelDataTypeSystem.DEFAULT);
    final RexBuilder rexBuilder = new RexBuilder(typeFactory);
    final VolcanoPlanner planner = new VolcanoPlanner();
    planner.addRelTraitDef(ConventionTraitDef.INSTANCE);
    final RelOptCluster cluster = RelOptCluster.create(planner, rexBuilder);
    final RelDataType inputRowType =
        typeFactory.builder().add("n", SqlTypeName.INTEGER).build();
    final RelDataType integerType = inputRowType.getFieldList().get(0).getType();
    final ImmutableList<ImmutableList<RexLiteral>> tuples =
        ImmutableList.of(
            ImmutableList.of(rexBuilder.makeExactLiteral(BigDecimal.ZERO,
                integerType)),
            ImmutableList.of(rexBuilder.makeExactLiteral(BigDecimal.ONE,
                integerType)),
            ImmutableList.of(rexBuilder.makeExactLiteral(BigDecimal.valueOf(2),
                integerType)));
    final EnumerableValues input =
        EnumerableValues.create(cluster, inputRowType, tuples);
    final MockSqlOperatorTable.CursorAndNumberTableFunction operator =
        new MockSqlOperatorTable.CursorAndNumberTableFunction();
    final RexNode cursor =
        rexBuilder.makeCall(SqlStdOperatorTable.CURSOR,
            rexBuilder.makeInputRef(inputRowType, 0));
    final RexCall call =
        (RexCall) rexBuilder.makeCall(operator, cursor,
            rexBuilder.makeExactLiteral(BigDecimal.TEN, integerType));
    final RelDataType outputRowType = typeFactory.builder()
        .add("CURSOR_VALUE", SqlTypeName.INTEGER)
        .add("NUMBER_VALUE", SqlTypeName.INTEGER)
        .build();
    final EnumerableTableFunctionScan scan =
        new EnumerableTableFunctionScan(cluster,
            cluster.traitSetOf(EnumerableConvention.INSTANCE),
            ImmutableList.of(input), Object[].class, outputRowType, call, null);
    final RexImplementorTable implementorTable =
        RexImplementorTables.chain(
            new SingleScalarTable(operator, operator.implementor()),
            RexImpTable.instance());
    final Map<String, Object> parameters = new HashMap<>();
    parameters.put("_rexImplementorTable", implementorTable);

    final Bindable<Object[]> bindable =
        EnumerableInterpretable.toBindable(parameters, null, scan,
            EnumerableRel.Prefer.ARRAY);
    final DataContext dataContext = new DataContext() {
      @Override public @Nullable SchemaPlus getRootSchema() {
        return null;
      }

      @Override public JavaTypeFactory getTypeFactory() {
        return typeFactory;
      }

      @Override public QueryProvider getQueryProvider() {
        return Linq4j.DEFAULT_PROVIDER;
      }

      @Override public @Nullable Object get(String name) {
        return parameters.get(name);
      }
    };
    final Enumerable<Object[]> rows = bindable.bind(dataContext);
    assertThat(rows.select(Arrays::toString).toList(),
        contains("[0, 10]", "[1, 11]", "[2, 12]"));
  }

  /** A table earlier in the chain overrides a built-in implementor. */
  @Test void earlierTableOverridesBuiltin() {
    final RexImplementorTable chain =
        RexImplementorTables.chain(
            new SingleScalarTable(SqlStdOperatorTable.UPPER, SENTINEL),
            RexImpTable.instance());
    assertThat(chain.get(SqlStdOperatorTable.UPPER), is(sameInstance(SENTINEL)));
  }

  /** A single-element chain returns that table itself, with no wrapper. */
  @Test void singleElementChainIsIdentity() {
    final RexImplementorTable table = new SingleScalarTable(MY_FN, SENTINEL);
    assertThat(RexImplementorTables.chain(table), is(sameInstance(table)));
  }

  /** An injected table drives project code generation for an operator that the
   * built-in table cannot translate on its own. */
  @Test void injectedTableDrivesProjectCodeGen() {
    final JavaTypeFactory typeFactory =
        new JavaTypeFactoryImpl(RelDataTypeSystem.DEFAULT);
    final RexBuilder rexBuilder = new RexBuilder(typeFactory);
    final RelDataType emptyRowType = typeFactory.builder().build();
    final RexNode call =
        rexBuilder.makeCall(MY_FN, rexBuilder.makeLiteral(true));
    final RexProgramBuilder programBuilder =
        new RexProgramBuilder(emptyRowType, rexBuilder);
    programBuilder.addProject(call, "c0");
    final RexProgram program = programBuilder.getProgram();
    final RexToLixTranslator.InputGetter inputGetter =
        (list, index, storageType) -> {
          throw new UnsupportedOperationException();
        };

    // The built-in table alone cannot translate MY_FN.
    assertThrows(RuntimeException.class, () ->
        RexToLixTranslator.translateProjects(program, typeFactory,
            SqlConformanceEnum.DEFAULT, new BlockBuilder(), null, null,
            DataContext.ROOT, inputGetter, null, RexImpTable.instance()));

    // A chained table that supplies MY_FN's implementor makes code-gen succeed.
    final RexCallImplementor implementor =
        RexImpTable.wrapAsRexCallImplementor(
            RexImpTable.createImplementor(
                (translator, c, operands) -> Expressions.constant(true),
                NullPolicy.NONE, false));
    final RexImplementorTable table =
        RexImplementorTables.chain(new SingleScalarTable(MY_FN, implementor),
            RexImpTable.instance());
    final List<Expression> expressions =
        RexToLixTranslator.translateProjects(program, typeFactory,
            SqlConformanceEnum.DEFAULT, new BlockBuilder(), null, null,
            DataContext.ROOT, inputGetter, null, table);
    assertThat(expressions, is(notNullValue()));
    assertThat(expressions, hasSize(1));
  }

  /** A chained extension table supplies an aggregate implementor that the
   * built-in table does not have, while still resolving built-in aggregates. */
  @Test void chainResolvesCustomAggregateImplementor() {
    final RexImplementorTable custom = new RexImplementorTable() {
      @Override public @Nullable RexCallImplementor get(SqlOperator operator) {
        return null;
      }

      @Override public @Nullable AggImplementor get(SqlAggFunction aggregation,
          boolean forWindowAggregate) {
        return aggregation == MY_AGG ? AGG_SENTINEL : null;
      }

      @Override public @Nullable MatchImplementor get(SqlMatchFunction function) {
        return null;
      }

      @Override public @Nullable TableFunctionCallImplementor get(
          SqlWindowTableFunction operator) {
        return null;
      }
    };
    final RexImplementorTable chain =
        RexImplementorTables.chain(custom, RexImpTable.instance());
    assertThat(RexImpTable.instance().get(MY_AGG, false), is(nullValue()));
    assertThat(chain.get(MY_AGG, false), is(sameInstance(AGG_SENTINEL)));
    assertThat(chain.get(SqlStdOperatorTable.COUNT, false), is(notNullValue()));
  }
}
