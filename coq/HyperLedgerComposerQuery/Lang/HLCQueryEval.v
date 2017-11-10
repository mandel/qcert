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

  (** Semantics of HLCQuery *)

  Context (h:brand_relation_t).
  Section eval.

    (* move to Utils/LiftIterators *)
    Fixpoint filter_map {A B} (f : A -> option B) (l:list A) : list B :=
      match l with
      | nil => nil
      | x :: t =>
        match f x with
        | None => filter_map f t
        | Some x' => x' :: (filter_map f t)
        end
      end.

    Definition hlcquery_statement_from_eval
               (b:registry_name) (registries: list (registry_name*(list data))) : option (list data)
      := lookup string_dec registries b.

    Definition hlcquery_datum := list (string*data).

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
             (params:list (string*data))
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
             (params:list (string*data))
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

    Definition hlcquery_statement_order_eval (order:hlcquery_ordering) (dl:list hlcquery_datum) : list hlcquery_datum
      := dl.

    Definition hlcquery_statement_skip_eval (skip:nat) (dl:list hlcquery_datum) :
      list hlcquery_datum
      := skipn skip dl.

    Definition hlcquery_statement_limit_eval (limit:nat) (dl:list hlcquery_datum) :
      list hlcquery_datum
      := firstn limit dl.

    Definition apply_optional {A} (f:(option (A -> A))) (a:A) : A
      := with_default f id a.
    
    Definition apply_optional_chain {A} (fl:list (option (A -> A))) (a:A) : A
      := fold_right apply_optional a fl.
    
    Import ListNotations.

    Definition hlcquery_statement_eval
               (q:hlcquery_statement)
               (registries: list (registry_name*(list data)))
               (params:list (string*data))
      : option (list hlcquery_datum)
      := let 'mk_hlcquery_statement select_brand reg_name cond ordering skip limit := q in
         bind (hlcquery_statement_from_eval
                 (with_default reg_name "default"%string) registries)
              (fun regdata =>
                 bind (hlcquery_statement_select_eval select_brand regdata)
                      (fun selected =>
                         let ofiltered :=
                           (match cond with
                            | Some c => hlcquery_condition_filter_eval c params selected
                            | None => Some selected
                            end) in
                         lift 
                           (apply_optional_chain [
                                  lift hlcquery_statement_order_eval ordering
                                  ; lift hlcquery_statement_skip_eval skip
                                  ; lift hlcquery_statement_limit_eval limit
                                ]) ofiltered
                      )
                 ).
    
    Definition hlcquery_eval (q:hlcquery)
               (registries: list (registry_name*(list data)))
               (params:list (string*data)) :option (list hlcquery_datum)
      := hlcquery_statement_eval (hlcquery_stmt q) registries params.

  End eval.

End HLCQueryEval.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
