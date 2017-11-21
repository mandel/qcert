(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

open QcertCompiler.EnhancedCompiler

val hlcquery_order_ASC : string -> QcertCompiler.hlcquery_order_col

val hlcquery_order_DESC : string -> QcertCompiler.hlcquery_order_col

val hlcquery_condition_expr_const : QData.qdata -> QcertCompiler.hlcquery_condition_expr

val hlcquery_condition_expr_param : string -> QcertCompiler.hlcquery_condition_expr

val hlcquery_condition_expr_var : string -> QcertCompiler.hlcquery_condition_expr

val hlcquery_condition_expr_unop :
    QcertCompiler.unary_op ->
      QcertCompiler.hlcquery_condition_expr -> QcertCompiler.hlcquery_condition_expr

val hlcquery_condition_expr_binop :
    QcertCompiler.binary_op ->
      QcertCompiler.hlcquery_condition_expr ->
	QcertCompiler.hlcquery_condition_expr ->
	  QcertCompiler.hlcquery_condition_expr

val hlcquery_condition_and :
    QcertCompiler.hlcquery_condition ->
      QcertCompiler.hlcquery_condition -> QcertCompiler.hlcquery_condition

val hlcquery_condition_or :
    QcertCompiler.hlcquery_condition ->
      QcertCompiler.hlcquery_condition -> QcertCompiler.hlcquery_condition

val hlcquery_condition_contains :
    QcertCompiler.hlcquery_condition_expr ->
      QcertCompiler.hlcquery_condition_expr -> QcertCompiler.hlcquery_condition

val hlcquery_condition_lifted_expr :
    QcertCompiler.hlcquery_condition_expr -> QcertCompiler.hlcquery_condition

val hlcquery_statement :
    QcertCompiler.brand ->
      QcertCompiler.registry_name option ->
	QcertCompiler.hlcquery_condition option ->
	  QcertCompiler.hlcquery_ordering option -> int option -> int option ->
	    QcertCompiler.hlcquery_statement

val hlcquery : string -> string -> QcertCompiler.hlcquery_statement -> QcertCompiler.hlcquery

val hlcq_of_hlcq_json : Hlcq_j.query -> QcertCompiler.hlcquery

