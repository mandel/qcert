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
  Require Import HLCQuerySemantics.
  Require Import HLCQueryEval.  
  Context {fruntime:foreign_runtime}.

  (* Proof that the semantic relation and evaluation function are the same *)

  Context (h:brand_relation_t).
  Section correctness.

    Lemma hlcquery_statement_from_sem_eval_same reg_name registries res :
      hlcquery_statement_from_sem reg_name registries res <->
      hlcquery_statement_from_eval (with_default reg_name hlcquery_statement_registry_default) registries = Some res.
    Proof.
      unfold hlcquery_statement_from_eval, with_default.
      split; intros.
      - invcs H; trivial.
      - match_destr_in H; constructor; trivial.
    Qed.

    Lemma hlcquery_statement_select_sem_eval_same b dl res :
      hlcquery_statement_select_sem h b dl res <->
      hlcquery_statement_select_eval h b dl = Some res.
    Proof.
      split; revert b res.
      - { induction dl; simpl in *; intros; inversion H; simpl; subst.
          - reflexivity.
          - rewrite hlcquery_statement_select_eval_cons_subrec; trivial.
            erewrite IHdl; eauto.
            reflexivity.
          - rewrite hlcquery_statement_select_eval_cons_nsub; trivial.
            erewrite IHdl; eauto.
        }
      - { induction dl; simpl in *; intros.
          - inversion H; subst; constructor.
          - destruct a; try solve [inversion H].
            destruct (sub_brands_dec h b0 (singleton b)) as [sub|nsub].
            + destruct (hlcquery_statement_select_eval_cons_sub_some_rec h sub H)
              ; subst.
              rewrite hlcquery_statement_select_eval_cons_subrec in H by trivial.
              apply some_lift in H; destruct H as [? ? ?]; subst.
              apply hlcquery_statement_select_sem_cons; auto.
            + rewrite hlcquery_statement_select_eval_cons_nsub in H by trivial.
              apply hlcquery_statement_select_sem_skip; auto.
        }
    Qed.

    Lemma hlcquery_condition_expr_sem_eval_same c params fields res :
      hlcquery_condition_expr_sem h c params fields res <->
      hlcquery_condition_expr_eval h c params fields = Some res.
    Proof.
      split; revert params fields res.
      - { induction c; simpl in *; intros; inversion H; simpl; subst; try eauto 3.
          - apply IHc in H2; rewrite H2; simpl; trivial.
          - apply IHc1 in H3; rewrite H3.
            apply IHc2 in H7; rewrite H7.
            simpl; trivial.
        }            
      - { induction c; simpl in *; intros.
          - inversion H; subst; constructor.
          - constructor; trivial.
          - constructor; trivial.
          - apply some_olift in H; destruct H as [? ev1 ?].
            apply IHc in ev1.
            econstructor; eauto.
          - apply some_olift2 in H; destruct H as [? [? [ev1 ev2] ?]].
            apply IHc1 in ev1.
            apply IHc2 in ev2.
            econstructor; eauto.
        }
    Qed.

    Lemma hlcquery_condition_sem_eval_same c params fields res :
      hlcquery_condition_sem h c params fields res <->
      hlcquery_condition_eval h c params fields = Some res.
    Proof.
      split; revert params fields res.
      - { induction c; simpl in *; intros; inversion H; simpl; subst.
          - apply IHc1 in H2; rewrite H2.
            apply IHc2  in H6; rewrite H6.
            simpl; trivial.
          - apply IHc1 in H2; rewrite H2.
            apply IHc2  in H6; rewrite H6.
            simpl; trivial.
          - apply hlcquery_condition_expr_sem_eval_same in H2; rewrite H2.
            apply hlcquery_condition_expr_sem_eval_same in H3; rewrite H3.
            simpl.
            destruct (in_dec data_eq_dec d l); tauto.
          - apply hlcquery_condition_expr_sem_eval_same in H2; rewrite H2.
            apply hlcquery_condition_expr_sem_eval_same in H3; rewrite H3.
            simpl.
            destruct (in_dec data_eq_dec d l); tauto.
          - apply hlcquery_condition_expr_sem_eval_same in H1; rewrite H1.
            trivial.
        }            
      - { induction c; simpl in *; intros.
          - apply some_olift2 in H; destruct H as [? [? [ev1 ev2] ?]].
            invcs e.
            constructor; eauto.
          - apply some_olift2 in H; destruct H as [? [? [ev1 ev2] ?]].
            invcs e.
            constructor; eauto.
          - match_case_in H; [intros ? eq1 | intros eq1]; rewrite eq1 in H; try discriminate.
            destruct d; try discriminate.
            invcs H.
            apply some_olift2 in eq1; destruct eq1 as [? [? [ev1 ev2] ?]].
            apply hlcquery_condition_expr_sem_eval_same in ev1.
            apply hlcquery_condition_expr_sem_eval_same in ev2.
            simpl in e.
            unfold ondcoll in e.
            destruct x0; try discriminate.
            invcs e.
            match_destr_in H0; invcs H0; econstructor; eauto.
          - match_case_in H; [intros ? eq1 | intros eq1]; rewrite eq1 in H; try discriminate.
            destruct d; try discriminate.
            invcs H.
            apply hlcquery_condition_expr_sem_eval_same in eq1.
            constructor; eauto.
        }
    Qed.

    Lemma hlcquery_condition_filter_sem_eval_same c params dl res :
      hlcquery_condition_filter_sem h c params dl res <->
      hlcquery_condition_filter_eval h c params dl = Some res.
    Proof.
      split; revert c params res.
      - { induction dl; simpl in *; intros; simpl; invcs H.
          - reflexivity.
          - apply hlcquery_condition_sem_eval_same in H4; rewrite H4.
            erewrite IHdl; eauto; reflexivity.
          - apply hlcquery_condition_sem_eval_same in H4; rewrite H4.
            erewrite IHdl; eauto; reflexivity.
        } 
      - { induction dl; simpl in *; intros.
          - invcs H; constructor.
          - apply some_lift2 in H; destruct H as [? [? [ev1 ev2] ?]].
            apply hlcquery_condition_sem_eval_same in ev1.
            apply IHdl in ev2.
            destruct x; subst; econstructor; eauto.
        }
    Qed.

    Lemma hlcquery_condition_filter_optional_sem_eval_same cond params dl res :
      hlcquery_condition_filter_optional_sem h cond params dl res <->
      (match cond with
                            | Some c => hlcquery_condition_filter_eval h c params dl
                            | None => Some dl
                            end) = Some res.
    Proof.
      split; intros.
      - invcs H; trivial.
        apply hlcquery_condition_filter_sem_eval_same; trivial.
      - destruct cond.
        + constructor.
          apply hlcquery_condition_filter_sem_eval_same; trivial.
        + invcs H.
          constructor.
    Qed.
    
    Lemma hlcquery_statement_order_sem_eval_same ord dl res :
      hlcquery_statement_order_sem ord dl res <->
      apply_optional (lift hlcquery_statement_order_eval ord) dl = res.
    Proof.
      unfold hlcquery_statement_order_eval, apply_optional, with_default.
      split; intros.
      - invcs H.
        destruct ord; simpl; reflexivity.
      - destruct ord; simpl in *; subst; constructor.
    Qed.

    Lemma hlcquery_statement_skip_sem_eval_same skip dl res :
      hlcquery_statement_skip_sem skip dl res <->
      apply_optional (lift hlcquery_statement_skip_eval skip) dl = res.
    Proof.
      unfold hlcquery_statement_skip_eval.
      split; intros.
      - destruct skip; simpl; invcs H; trivial.
      - destruct skip; simpl in *; subst; constructor.
    Qed.

    Lemma hlcquery_statement_limit_sem_eval_same limit dl res :
      hlcquery_statement_limit_sem limit dl res <->
      apply_optional (lift hlcquery_statement_limit_eval limit) dl = res.
    Proof.
      unfold hlcquery_statement_limit_eval.
      split; intros.
      - destruct limit; simpl; invcs H; trivial.
      - destruct limit; simpl in *; subst; constructor.
    Qed.
    
    Lemma hlcquery_statement_sem_eval_same stmt registries params res :
      hlcquery_statement_sem h stmt registries params res <->
      hlcquery_statement_eval h stmt registries params = Some res.
    Proof.
      unfold hlcquery_statement_eval.
      destruct stmt.
      split; intros.
      - invcs H.
        apply hlcquery_statement_from_sem_eval_same in H6; rewrite H6; simpl.
        apply hlcquery_statement_select_sem_eval_same in H10; rewrite H10; simpl.
        apply hlcquery_condition_filter_optional_sem_eval_same in H11; rewrite H11; simpl.
        apply hlcquery_statement_order_sem_eval_same in H12; rewrite H12; simpl.
        apply hlcquery_statement_skip_sem_eval_same in H13; rewrite H13; simpl.
        apply hlcquery_statement_limit_sem_eval_same in H14; rewrite H14; simpl.
        trivial.
      - unfold bind in H.
        apply some_olift in H.
        destruct H as [? from rest].
        apply hlcquery_statement_from_sem_eval_same in from.
        symmetry in rest.
        apply some_olift in rest.
        destruct rest as [? sel rest].
        apply hlcquery_statement_select_sem_eval_same in sel.
        symmetry in rest.
        apply some_olift in rest.
        destruct rest as [? filter rest].
        apply hlcquery_condition_filter_optional_sem_eval_same in filter.
        invcs rest.
        eapply hlcquery_statement_sem_holds; eauto.
        + eapply hlcquery_statement_order_sem_eval_same;  eauto.
        + eapply hlcquery_statement_skip_sem_eval_same; eauto.
        + eapply hlcquery_statement_limit_sem_eval_same; eauto.
    Qed.

    Theorem hlcquery_sem_eval_same q registries params res :
      hlcquery_sem h q registries params res <->
      hlcquery_eval h q registries params = Some res.
    Proof.
      unfold hlcquery_eval; simpl.
      split; intros.
      - invcs H; simpl.
        apply hlcquery_statement_sem_eval_same; trivial.
      - destruct q; constructor; apply hlcquery_statement_sem_eval_same; trivial.
    Qed.

  End correctness.

End HLCQuerySemantics.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "Qcert")) ***
*** End: ***
*)
