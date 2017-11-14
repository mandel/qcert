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

Section HLCQuerySemantics.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  Require Import HLCQueryDef.
  Require Import HLCQueryDec.
  
  Context {fruntime:foreign_runtime}.

  (** Semantics for HLCQuery *)

  Context (h:brand_relation_t).
  Section sem.

    Inductive hlcquery_statement_from_sem :
      option registry_name ->
      list (registry_name*(list data)) ->
      list data ->
      Prop :=
    | hlcquery_statement_from_sem_default registries reg :
        lookup string_dec registries "default"%string = Some reg ->
        hlcquery_statement_from_sem None registries reg
    | hlcquery_statement_from_sem_some registries regname reg :
        lookup string_dec registries regname = Some reg ->
        hlcquery_statement_from_sem (Some regname) registries reg.

    Inductive hlcquery_statement_select_sem :
              brand -> list data -> list (hlcquery_datum) -> Prop
      :=
      | hlcquery_statement_select_sem_nil b :
           hlcquery_statement_select_sem b nil nil
      | hlcquery_statement_select_sem_cons b b' r dl res :
          sub_brands h b' (singleton b) ->
          hlcquery_statement_select_sem b dl res ->
          hlcquery_statement_select_sem b (dbrand b' (drec r)::dl) (r::res)
      | hlcquery_statement_select_sem_skip b b' d dl res :
          ~ sub_brands h b' (singleton b) ->
          hlcquery_statement_select_sem b dl res ->
          hlcquery_statement_select_sem b (dbrand b' d::dl) res.

    Inductive hlcquery_condition_expr_sem
      : hlcquery_condition_expr ->
        list (string*data) ->
        list (string*data) ->
        data ->
        Prop :=
    | hlcquery_condition_expr_sem_const d params fields:
        hlcquery_condition_expr_sem (hlcquery_condition_expr_const d) params fields d
    | hlcquery_condition_expr_sem_param p params fields d:
        lookup string_dec params p = Some d ->
        hlcquery_condition_expr_sem (hlcquery_condition_expr_param p) params fields d
    | hlcquery_condition_expr_sem_var v params fields d:
        lookup string_dec fields v = Some d ->
        hlcquery_condition_expr_sem (hlcquery_condition_expr_var v) params fields d
    | hlcquery_condition_expr_sem_unop u c1 d1 params fields d:
        hlcquery_condition_expr_sem c1 params fields d1 ->
        unary_op_eval h u d1 = Some d ->
        hlcquery_condition_expr_sem (hlcquery_condition_expr_unop u c1) params fields d
    | hlcquery_condition_expr_sem_binop b c1 d1 c2 d2 params fields d:
        hlcquery_condition_expr_sem c1 params fields d1 ->
        hlcquery_condition_expr_sem c2 params fields d2 ->
        binary_op_eval h b d1 d2 = Some d ->
        hlcquery_condition_expr_sem (hlcquery_condition_expr_binop b c1 c2) params fields d
    .
    
    Inductive hlcquery_condition_sem :
      hlcquery_condition ->
      list (string*data) ->
      list (string*data) ->
      bool ->
      Prop :=
    | hlcquery_condition_sem_and c1 c2 params fields b1 b2 :
        hlcquery_condition_sem c1 params fields b1 ->
        hlcquery_condition_sem c2 params fields b2 ->
        hlcquery_condition_sem (hlcquery_condition_and c1 c2) params fields (andb b1 b2)
    | hlcquery_condition_sem_or c1 c2 params fields b1 b2 :
        hlcquery_condition_sem c1 params fields b1 ->
        hlcquery_condition_sem c2 params fields b2 ->
        hlcquery_condition_sem (hlcquery_condition_or c1 c2) params fields (orb b1 b2)
    | hlcquery_condition_sem_contains_true ce1 ce2 params fields d l :
        hlcquery_condition_expr_sem ce1 params fields d ->
        hlcquery_condition_expr_sem ce2 params fields (dcoll l) ->
        In d l ->
        hlcquery_condition_sem (hlcquery_condition_contains ce1 ce2) params fields true
    | hlcquery_condition_sem_contains_false ce1 ce2 params fields d l :
        hlcquery_condition_expr_sem ce1 params fields d ->
        hlcquery_condition_expr_sem ce2 params fields (dcoll l) ->
        ~ In d l ->
        hlcquery_condition_sem (hlcquery_condition_contains ce1 ce2) params fields false
    | hlcquery_condition_sem_lifted ce params fields b  :
        hlcquery_condition_expr_sem ce params fields (dbool b) ->
        hlcquery_condition_sem (hlcquery_condition_lifted_expr ce) params fields b
    .

    Inductive hlcquery_condition_filter_sem :
      hlcquery_condition ->
      list (string*data) ->
      list hlcquery_datum ->
      list hlcquery_datum ->
      Prop
      :=
      | hlcquery_condition_filter_sem_nil cond params:
           hlcquery_condition_filter_sem cond params nil nil
      | hlcquery_condition_filter_sem_cons cond params d dl res :
          hlcquery_condition_sem cond params d true ->
          hlcquery_condition_filter_sem cond params dl res ->
          hlcquery_condition_filter_sem cond params (d::dl) (d::res)
      | hlcquery_condition_filter_sem_skip cond params d dl res :
          hlcquery_condition_sem cond params d false ->
          hlcquery_condition_filter_sem cond params dl res ->
          hlcquery_condition_filter_sem cond params (d::dl) res.

    Inductive hlcquery_condition_filter_optional_sem :
      option (hlcquery_condition) ->
      list (string*data) ->
      list hlcquery_datum ->
      list hlcquery_datum ->
      Prop :=
      | hlcquery_condition_filter_optional_sem_none params dl :
           hlcquery_condition_filter_optional_sem None params dl dl
      |  hlcquery_condition_filter_optional_sem_some c params dl res :
         hlcquery_condition_filter_sem c params dl res ->
         hlcquery_condition_filter_optional_sem (Some c) params dl res
    .
    
    Definition hlcquery_statement_order_sem (order:option hlcquery_ordering) (dl:list hlcquery_datum) (res:list hlcquery_datum)
      := dl = res.

    Inductive hlcquery_statement_skip_sem :
      option nat ->
      list hlcquery_datum ->
      list hlcquery_datum ->
      Prop :=
    |  hlcquery_statement_skip_sem_none dl :
         hlcquery_statement_skip_sem None dl dl
    |  hlcquery_statement_skip_sem_some skip dl :
         hlcquery_statement_skip_sem (Some skip) dl (skipn skip dl)
    .

    Inductive hlcquery_statement_limit_sem :
      option nat ->
      list hlcquery_datum ->
      list hlcquery_datum ->
      Prop :=
    |  hlcquery_statement_limit_sem_none dl :
         hlcquery_statement_limit_sem None dl dl
    |  hlcquery_statement_limit_sem_some limit dl :
         hlcquery_statement_limit_sem (Some limit) dl (firstn limit dl)
    .

    Inductive hlcquery_statement_sem :
      hlcquery_statement ->
      list (registry_name*(list data)) ->
      list (string*data) ->
      list hlcquery_datum ->
      Prop :=
    | hlcquery_statement_sem_holds
        select_brand reg_name cond ordering skip limit
        registries params
        regdata
        selected
        filtered
        ordered
        skipped
        result
      :
        hlcquery_statement_from_sem reg_name registries regdata ->
        hlcquery_statement_select_sem select_brand regdata selected ->
        hlcquery_condition_filter_optional_sem cond params selected filtered ->
        hlcquery_statement_order_sem ordering filtered ordered ->
        hlcquery_statement_skip_sem skip ordered skipped ->
        hlcquery_statement_limit_sem limit skipped result ->
          hlcquery_statement_sem
          (mk_hlcquery_statement select_brand reg_name cond ordering skip limit)
          registries
          params
          result.

    Inductive hlcquery_sem :
      hlcquery ->
      list (registry_name*(list data)) ->
      list (string*data) ->
      list hlcquery_datum ->
      Prop := 
    | hlcquery_sem_holds
        name desc stmt
        registries params res :
        hlcquery_statement_sem stmt registries params res ->
        hlcquery_sem (mk_hlcquery name desc stmt) registries params res.

  End sem.

End HLCQuerySemantics.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
