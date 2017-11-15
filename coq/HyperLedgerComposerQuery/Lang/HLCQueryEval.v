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

Section HLCQueryEval.
  Require Import String.
  Require Import List.
  Require Import Arith.
  Require Import EquivDec.
  Require Import Utils.
  Require Import CommonRuntime.

  Require Import HLCQueryDef.
  Require Import HLCQueryDec.
  
  Context {fruntime:foreign_runtime}.

  (** Evaluator for HLCQuery *)

  Context (h:brand_relation_t).
  Section eval.

    Definition hlcquery_statement_from_eval
               (b:registry_name) (registries: list (registry_name*(list data))) : option (list data)
      := lookup string_dec registries b.

    (* We want to differentiate having the wrong brand 
       (filtered out) from having the right brand but not being a record
       (a hard error) *)
    Definition hlcquery_statement_select_eval (b:brand) (dl:list data)
      : option (list hlcquery_datum)
      := let brand_list := 
             lift_map
                 (fun d =>
                    match d with
                    | dbrand br r => Some (br, r)
                    | _ => None
                    end)
                 dl in
         let filtered_list :=
             lift (filter_map
               (fun d => let '(br, r) := d in
                         if (sub_brands_dec h br (singleton b))
                         then Some r
                         else None)) brand_list in
         let rec_list := olift (lift_map
           (fun d => 
              match d with
              | drec r => Some r
              | _ => None
              end)) filtered_list in
         rec_list.

    (* again, we differentiate false from error *)
    Fixpoint hlcquery_condition_expr_eval
             (cond:hlcquery_condition_expr)
             (params:hlcquery_params)
             (fields:list (string*data))
      : option data
      := match cond with
         | hlcquery_condition_expr_const d => Some d
         | hlcquery_condition_expr_param p => lookup string_dec params p
         | hlcquery_condition_expr_var v => lookup string_dec fields v
         | hlcquery_condition_expr_unop u c1 =>
           olift (unary_op_eval h u)
                 (hlcquery_condition_expr_eval c1 params fields)
         | hlcquery_condition_expr_binop b c1 c2 =>
           olift2 (binary_op_eval h b)
                  (hlcquery_condition_expr_eval c1 params fields)
                  (hlcquery_condition_expr_eval c2 params fields)
         end.

    Fixpoint hlcquery_condition_eval
             (cond:hlcquery_condition)
             (params fields:list (string*data))
      : option bool
      := match cond with
         | hlcquery_condition_and c1 c2 =>
           lift2 andb
                 (hlcquery_condition_eval c1 params fields)
                 (hlcquery_condition_eval c2 params fields)
         | hlcquery_condition_or c1 c2 =>
           lift2 orb
                 (hlcquery_condition_eval c1 params fields)
                 (hlcquery_condition_eval c2 params fields)
         | hlcquery_condition_contains ce1 ce2 =>
           match hlcquery_condition_expr_eval
                   (hlcquery_condition_expr_binop OpContains ce1 ce2) params fields with
           | Some (dbool b) => Some b
           | _ => None
           end
         | hlcquery_condition_lifted_expr ce =>
           match hlcquery_condition_expr_eval ce params fields with
           | Some (dbool b) => Some b
           | _ => None
           end
         end.

    Fixpoint hlcquery_condition_filter_eval
             (cond:hlcquery_condition)
             (params:hlcquery_params)
             (dl:list hlcquery_datum) : option (list hlcquery_datum)
      := match dl with
         | nil => Some nil
         | d::dl' => lift2 (fun (ob:bool) (ol:list hlcquery_datum) =>
                               if ob
                               then d::ol
                               else ol)
                       (hlcquery_condition_eval cond params d)
                       (hlcquery_condition_filter_eval cond params dl')
         end.

    (* TODO *)
    Definition hlcquery_statement_order_eval (order:hlcquery_ordering) (dl:list hlcquery_datum) : list hlcquery_datum
      := dl.

    Definition hlcquery_statement_skip_eval (skip:nat) (dl:list hlcquery_datum) :
      list hlcquery_datum
      := skipn skip dl.

    Definition hlcquery_statement_limit_eval (limit:nat) (dl:list hlcquery_datum) :
      list hlcquery_datum
      := firstn limit dl.
    
    Definition hlcquery_statement_eval
               (q:hlcquery_statement)
               (registries: list (registry_name*(list data)))
               (params:hlcquery_params)
      : option (list hlcquery_datum)
      := let 'mk_hlcquery_statement select_brand reg_name cond ordering skip limit := q in
         bind (hlcquery_statement_from_eval
                 (with_default reg_name hlcquery_statement_registry_default) registries)
              (fun regdata =>
                 bind (hlcquery_statement_select_eval select_brand regdata)
                      (fun selected =>
                         let ofiltered :=
                           (match cond with
                            | Some c => hlcquery_condition_filter_eval c params selected
                            | None => Some selected
                            end) in
                         bind ofiltered (fun filtered =>
                         let ordered := apply_optional (lift hlcquery_statement_order_eval ordering) filtered in
                         let skipped := apply_optional (lift hlcquery_statement_skip_eval skip) ordered in
                         let limited :=  apply_optional (lift hlcquery_statement_limit_eval limit) skipped in
                         Some limited))
                 ).
    
    Definition hlcquery_eval (q:hlcquery)
               (registries: list (registry_name*(list data)))
               (params:hlcquery_params) :option (list hlcquery_datum)
      := hlcquery_statement_eval (hlcquery_stmt q) registries params.

    Definition bindings_to_registries (env:bindings) : option (list (registry_name*(list data)))
      := lift_map (fun kv => lift (fun v' => (fst kv, v')) (ondcoll id (snd kv))) env.

    Definition eval_hlcquery_top (q:hlcquery) (params:hlcquery_params) (cenv: bindings) : option data
      := lift (fun results => dcoll (map drec results))
              (bind (bindings_to_registries cenv)
                    (fun registries => hlcquery_eval q registries params)).

    Definition undrec (d:data) : option (list (string * data))
      := match d with
         | drec r => Some r
         | _ => None
         end.
    
    Definition eval_hlcquery_top_curried (q:hlcquery) (input: bindings) : option data
      := bind
           (lookup string_dec input "registries"%string)
           (fun regdata =>
              bind (undrec regdata)
                   (fun registries =>
                      bind (lookup string_dec input "parameters"%string)
                           (fun paramsdata =>
                              bind (undrec paramsdata)
                                   (fun params =>
                                      eval_hlcquery_top q params registries)))).

  End eval.

  Section evalprops.

    Lemma hlcquery_statement_select_eval_cons_subrec (b:brand) (b':brands) r (dl:list data)
      : sub_brands h b' (singleton b) ->
        hlcquery_statement_select_eval b (dbrand b' (drec r) :: dl) =
          lift (cons r) (hlcquery_statement_select_eval b dl)
    .
    Proof.
      unfold hlcquery_statement_select_eval.
      simpl.
      generalize ((lift_map
             (fun d : data =>
              match d with
              | dunit => None
              | dnat _ => None
              | dbool _ => None
              | dstring _ => None
              | dcoll _ => None
              | drec _ => None
              | dleft _ => None
              | dright _ => None
              | dbrand br r0 => Some (br, r0)
              | dforeign _ => None
              end) dl)); intro abs.
      destruct abs; simpl; trivial.
      generalize ((filter_map
                     (fun '(br, r0) => if sub_brands_dec h br (singleton b) then Some r0 else None) l)); intros dl'.
      destruct (sub_brands_dec h b' (singleton b)); simpl; tauto.
    Qed.

    Lemma hlcquery_statement_select_eval_cons_nsub
          (b:brand) (b':brands) d (dl:list data)
      : ~ sub_brands h b' (singleton b) -> 
        hlcquery_statement_select_eval b (dbrand b' d :: dl) =
        hlcquery_statement_select_eval b dl
    .
    Proof.
      unfold hlcquery_statement_select_eval.
      simpl.
      generalize ((lift_map
             (fun d : data =>
              match d with
              | dunit => None
              | dnat _ => None
              | dbool _ => None
              | dstring _ => None
              | dcoll _ => None
              | drec _ => None
              | dleft _ => None
              | dright _ => None
              | dbrand br r0 => Some (br, r0)
              | dforeign _ => None
              end) dl)); intro abs.
      destruct abs; simpl; trivial.
      generalize ((filter_map
                       (fun '(br, r0) => if sub_brands_dec h br (singleton b) then Some r0 else None) l)); intros dl'.
      destruct (sub_brands_dec h b' (singleton b)); try tauto.
    Qed.

    Lemma hlcquery_statement_select_eval_cons_sub_some_rec {b:brand} {b':brands} {d} {dl:list data} {res}
      : sub_brands h b' (singleton b) ->
        hlcquery_statement_select_eval b (dbrand b' d :: dl) = Some res ->
        exists r, d = drec r.
    Proof.
      unfold hlcquery_statement_select_eval; simpl.
      generalize ((lift_map
             (fun d : data =>
              match d with
              | dunit => None
              | dnat _ => None
              | dbool _ => None
              | dstring _ => None
              | dcoll _ => None
              | drec _ => None
              | dleft _ => None
              | dright _ => None
              | dbrand br r0 => Some (br, r0)
              | dforeign _ => None
              end) dl)); intro abs.
      destruct abs; simpl; try discriminate.
      generalize ((filter_map
                     (fun '(br, r0) => if sub_brands_dec h br (singleton b) then Some r0 else None) l)); intros dl'.
      destruct (sub_brands_dec h b' (singleton b)); simpl; try tauto.
      destruct d; try discriminate.
      eauto.
    Qed.

    End evalprops.

End HLCQueryEval.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
