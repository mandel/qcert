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

(* decidable equality for the language statements *)

Section HLCQueryDec.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  Require Import HLCQueryDef.

  Context {fruntime:foreign_runtime}.
  
  Global Instance hlcquery_order_col_eqdec : EqDec hlcquery_order_col eq.
  Proof.
    change (forall x y: hlcquery_order_col,  {x = y} + {x <> y}).
    decide equality; solve [apply string_eqdec].
  Defined.

  Global Instance hlcquery_ordering_eqdec : EqDec hlcquery_ordering eq.
  Proof.
    apply list_eqdec. apply hlcquery_order_col_eqdec.
  Defined.

  Global Instance hlcquery_condition_expr_eqdec : EqDec  hlcquery_condition_expr eq.
  Proof.
    change (forall x y: hlcquery_condition_expr,  {x = y} + {x <> y}).
    decide equality; solve [
                         apply string_eqdec
                       | apply data_eqdec
                       | apply unary_op_eqdec
                       | apply binary_op_eqdec
                       ].
  Defined.

  Global Instance hlcquery_condition_eqdec : EqDec  hlcquery_condition eq.
  Proof.
    change (forall x y: hlcquery_condition,  {x = y} + {x <> y}).
    decide equality; solve [apply hlcquery_condition_expr_eqdec].
  Defined.

  Global Instance hlcquery_statement_eqdec : EqDec  hlcquery_statement eq.
  Proof.
    change (forall x y: hlcquery_statement,  {x = y} + {x <> y}).
    decide equality;
      try apply option_eqdec;
      try solve [
            apply string_eqdec
          | apply hlcquery_condition_expr_eqdec
          | apply hlcquery_ordering_eqdec
          | apply hlcquery_condition_eqdec
          ].
  Defined.

  Global Instance hlcquery_eqdec : EqDec  hlcquery eq.
  Proof.
    change (forall x y: hlcquery,  {x = y} + {x <> y}).
    decide equality;
      try solve [
            apply string_eqdec
          | apply hlcquery_statement_eqdec
          ].
  Defined.

End HLCQueryDec.

(* 
 *** Local Variables: ***
 *** coq-load-path: (("../../../coq" "Qcert")) ***
 *** End: ***
 *)
