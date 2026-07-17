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
package org.apache.calcite.sql.util;

import org.apache.calcite.linq4j.Enumerable;
import org.apache.calcite.rel.type.RelDataType;

import static java.util.Objects.requireNonNull;

/** Utilities for creating {@link CursorInput} instances. */
public final class CursorInputs {
  private CursorInputs() {
  }

  /** Creates a cursor input. */
  public static CursorInput of(RelDataType rowType, Enumerable<Object[]> rows) {
    return new CursorInputImpl(rowType, rows);
  }

  /** Default implementation of {@link CursorInput}. */
  private static class CursorInputImpl implements CursorInput {
    private final RelDataType rowType;
    private final Enumerable<Object[]> rows;

    CursorInputImpl(RelDataType rowType, Enumerable<Object[]> rows) {
      this.rowType = requireNonNull(rowType, "rowType");
      this.rows = requireNonNull(rows, "rows");
    }

    @Override public RelDataType getRowType() {
      return rowType;
    }

    @Override public Enumerable<Object[]> rows() {
      return rows;
    }
  }
}
