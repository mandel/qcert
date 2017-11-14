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

Section HLCQuerySize.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  Require Import HLCQueryDef.
  Context {fruntime:foreign_runtime}.

  Fixpoint hlcquery_condition_expr_size (e:hlcquery_condition_expr) : nat
    := match e with
       | hlcquery_condition_expr_const _ => 1
       | hlcquery_condition_expr_param _ => 1
       | hlcquery_condition_expr_var _ => 1
       | hlcquery_condition_expr_unop _ e1 => S (hlcquery_condition_expr_size e1)
       | hlcquery_condition_expr_binop _ e1 e2 => S (hlcquery_condition_expr_size e1 + hlcquery_condition_expr_size e2)
       end.

  Fixpoint  hlcquery_condition_size (c: hlcquery_condition) : nat
    := match c with 
       | hlcquery_condition_and c1 c2 =>S (hlcquery_condition_size c1 + hlcquery_condition_size c2)
       | hlcquery_condition_or c1 c2 => S (hlcquery_condition_size c1 + hlcquery_condition_size c2)
       | hlcquery_condition_contains e1 e2 => S (hlcquery_condition_expr_size e1 + hlcquery_condition_expr_size e2)
       | hlcquery_condition_lifted_expr e1 => hlcquery_condition_expr_size e1
       end.

  (* For now, assume that ordering and the other stuff is free *)
  Definition hlcquery_statement_size (s:hlcquery_statement) : nat
    := S
      match (hlcquery_statement_where s) with
      | Some c => hlcquery_condition_size c
      | None => 0
      end.

  Definition hlcquery_size (q:hlcquery) : nat
    := hlcquery_statement_size (hlcquery_stmt q).

  
End HLCQuerySize.


(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
