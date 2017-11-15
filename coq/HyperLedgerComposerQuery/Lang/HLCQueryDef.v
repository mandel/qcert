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

Section HLCQueryDef.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  Context {fruntime:foreign_runtime}.

  Definition registry_name := string.

  Inductive hlcquery_order_col : Set :=
  | hlcquery_order_ASC : string -> hlcquery_order_col
  | hlcquery_order_DESC : string -> hlcquery_order_col.

  Definition hlcquery_ordering := list hlcquery_order_col.

  (* I really have no idea what is actually allowed, so far now just reuse our existing operators *)
  Inductive hlcquery_condition_expr : Set :=
  | hlcquery_condition_expr_const : data -> hlcquery_condition_expr
  | hlcquery_condition_expr_param : string -> hlcquery_condition_expr
  | hlcquery_condition_expr_var : string -> hlcquery_condition_expr
  | hlcquery_condition_expr_unop : unary_op -> hlcquery_condition_expr -> hlcquery_condition_expr
  | hlcquery_condition_expr_binop : binary_op -> hlcquery_condition_expr -> hlcquery_condition_expr -> hlcquery_condition_expr
  .
      
  Inductive hlcquery_condition : Set :=
  | hlcquery_condition_and : hlcquery_condition ->  hlcquery_condition ->  hlcquery_condition
  | hlcquery_condition_or : hlcquery_condition ->  hlcquery_condition ->  hlcquery_condition
  | hlcquery_condition_contains : hlcquery_condition_expr ->  hlcquery_condition_expr ->  hlcquery_condition
  | hlcquery_condition_lifted_expr : hlcquery_condition_expr -> hlcquery_condition.
  
  Record hlcquery_statement : Set :=
    mk_hlcquery_statement {
      hlcquery_statement_select: brand;
      hlcquery_statement_from: option registry_name;
      hlcquery_statement_where : option hlcquery_condition;
      hlcquery_statement_order_by: option hlcquery_ordering;
      hlcquery_statement_skip: option nat;
      hlcquery_statement_limit: option nat;
    }.

  Record hlcquery : Set
    := mk_hlcquery {
        hlcquery_name: string;
        hlcquery_description: string;
        hlcquery_stmt: hlcquery_statement
      }.

  Definition hlcquery_datum := list (string*data).
  Definition hlcquery_params := list (string*data).

  (* TODO: this is not currently used; our current default is ∞ *)
  Definition hlcquery_statement_limit_default : nat
    := 25.

  Definition hlcquery_statement_registry_default : string
    := "default"%string.

End HLCQueryDef.
(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
