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

Require Import String.
Require Import HLCQueryRuntime.
Require Import CompilerRuntime.
Require Import QData.
Require Import QOperators.

Module QHLCQ(runtime:CompilerRuntime).

  Module Data := QData.QData runtime.
  Module Ops := QOperators.QOperators runtime.

  Definition hlcquery_order_ASC := hlcquery_order_ASC.
  Definition hlcquery_order_DESC := hlcquery_order_DESC.

  Definition hlcquery_condition_expr_const := hlcquery_condition_expr_const.
  Definition hlcquery_condition_expr_param := hlcquery_condition_expr_param.
  Definition hlcquery_condition_expr_var := hlcquery_condition_expr_var.
  Definition hlcquery_condition_expr_unop := hlcquery_condition_expr_unop.
  Definition hlcquery_condition_expr_binop := hlcquery_condition_expr_binop.

  Definition hlcquery_condition_and := hlcquery_condition_and.
  Definition hlcquery_condition_or := hlcquery_condition_or.
  Definition hlcquery_condition_contains := hlcquery_condition_contains.
  Definition hlcquery_condition_lifted_expr := hlcquery_condition_lifted_expr.

  Definition hlcquery_statement := mk_hlcquery_statement.

  Definition hlcquery := mk_hlcquery.

End QHLCQ.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
