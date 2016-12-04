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

Section NRAEnvtoNNRCExt.

  (* begin hide *)
  Require Import String.
  Require Import List.
  Require Import EquivDec.
  Require Import Compare_dec.

  Require Import Utils BasicRuntime.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime.
  Require Import NRAEnvtoNNRC.

  (* end hide *)

  Context {fruntime:foreign_runtime}.

  (** Translation from NRAEnv to Named Nested Relational Calculus Extended *)
  Fixpoint nraenv_to_nnrc_ext (op:nraenv) (varid varenv:var) : nnrc :=
    match op with
    (* [[ ID ]]_vid,venv == vid *)
    | NRAEnvID => NNRCVar varid
    (* [[ Const ]]_vid,venv == Const *)
    | NRAEnvConst rd => NNRCConst rd
    (* [[ op1 ⊕ op2 ]]_vid,venv == [[ op1 ]]_vid,venv ⊕ [[ op2 ]]_vid,venv *)
    | NRAEnvBinop bop op1 op2 =>
      NNRCBinop bop (nraenv_to_nnrc_ext op1 varid varenv) (nraenv_to_nnrc_ext op2 varid varenv)
    (* [[ UOP op1 ]]_vid,venv = UOP [[ op1 ]]_vid,venv *)
    | NRAEnvUnop uop op1 =>
      NNRCUnop uop (nraenv_to_nnrc_ext op1 varid varenv)
    (* [[ χ⟨ op1 ⟩( op2 ) ]]_vid,venv = { [[ op1 ]]_t,venv | t ∈ [[ op2 ]]_vid,venv } *)
    | NRAEnvMap op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tmap$" (varid::varenv::nil) in
      NNRCFor t nrc2 (nraenv_to_nnrc_ext op1 t varenv)
    (* [[ ⋈ᵈ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op1 ]]_t1,venv } | t1 ∈ [[ op2 ]]_vid,venv } *)
    | NRAEnvMapConcat op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let (t1,t2) := fresh_var2 "tmc$" "tmc$" (varid::varenv::nil) in
      NNRCUnop AFlatten
              (NNRCFor t1 nrc2
                      (NNRCFor t2 (nraenv_to_nnrc_ext op1 t1 varenv)
                              ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
    (* [[ op1 × op2 ]]_vid,venv
               == ⋃{ { t1 ⊕ t2 | t2 ∈ [[ op2 ]]_vid,venv } | t1 ∈ [[ op1 ]]_vid,venv } *)
    | NRAEnvProduct op1 op2 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let (t1,t2) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
      NNRCUnop AFlatten
              (NNRCFor t1 nrc1
                      (NNRCFor t2 nrc2
                              ((NNRCBinop AConcat) (NNRCVar t1) (NNRCVar t2))))
    (* [[ σ⟨ op1 ⟩(op2) ]]_vid,venv
               == ⋃{ if [[ op1 ]]_t1,venv then { t1 } else {} | t1 ∈ [[ op2 ]]_vid,venv } *)
    | NRAEnvSelect op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tsel$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 t varenv) in
      NNRCUnop AFlatten
              (NNRCFor t nrc2
                      (NNRCIf nrc1 (NNRCUnop AColl (NNRCVar t)) (NNRCConst (dcoll nil))))
    (* [[ op1 ∥ op2 ]]_vid,venv == let t := [[ op1 ]]_vid,venv in
                                       if (t = {})
                                       then [[ op2 ]]_vid,venv
                                       else t *)
    | NRAEnvDefault op1 op2 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tdef$" (varid::varenv::nil) in
      (NNRCLet t nrc1
              (NNRCIf (NNRCBinop AEq
                               (NNRCVar t)
                               (NNRCUnop AFlatten (NNRCConst (dcoll nil))))
                     nrc2 (NNRCVar t)))
    (* [[ op1 ◯ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                     in [[ op1 ]]_t,venv *)
    | NRAEnvEither opl opr =>
      let (t1,t2) := fresh_var2 "teitherL$" "teitherR$" (varid::varenv::nil) in
      let nrcl := (nraenv_to_nnrc_ext opl t1 varenv) in
      let nrcr := (nraenv_to_nnrc_ext opr t2 varenv) in
      NNRCEither (NNRCVar varid) t1 nrcl t2 nrcr
    | NRAEnvEitherConcat op1 op2 =>
      let nrc1 := (nraenv_to_nnrc_ext op1 varid varenv) in
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tec$" (varid::varenv::nil) in 
      NNRCLet t nrc2
             (NNRCEither nrc1 varid (NNRCUnop ALeft (NNRCBinop AConcat (NNRCVar varid) (NNRCVar t)))
                        varid (NNRCUnop ARight (NNRCBinop AConcat (NNRCVar varid) (NNRCVar t))))
    | NRAEnvApp op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tapp$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 t varenv) in
      (NNRCLet t nrc2 nrc1)
    (* [[ CENV v ]]_vid,venv = v *)
    | NRAEnvGetConstant s => NNRCVar (append CONST_PREFIX s)
    (* [[ ENV ]]_vid,venv = venv *)
    | NRAEnvEnv => NNRCVar varenv
    (* [[ op1 ◯ₑ op2 ]]_vid,venv == let t := [[ op2 ]]_vid,venv
                                      in [[ op1 ]]_vid,t *)
    | NRAEnvAppEnv op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tappe$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 varid t) in
      (NNRCLet t nrc2 nrc1)
    (* [[ χᵉ⟨ op1 ⟩ ]]_vid,venv = { [[ op1 ]]_vid,t1 | t1 ∈ venv } *)
    | NRAEnvMapEnv op1 =>
      let t1 := fresh_var "tmape$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 varid t1) in
      (NNRCFor t1 (NNRCVar varenv) nrc1)
    (* [[ χᵉ⟨ op1 ⟩ ]]_vid,venv = ♯flatten({ [[ op1 ]]_vid,t1 | t1 ∈ venv }) *)
    | NRAEnvFlatMap op1 op2 =>
      let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
      let t := fresh_var "tmap$" (varid::varenv::nil) in
      NNRCUnop AFlatten (NNRCFor t nrc2 (nraenv_to_nnrc_ext op1 t varenv))
    | NRAEnvJoin op1 op2 op3 =>
      let nrc2 :=
          let nrc2 := (nraenv_to_nnrc_ext op2 varid varenv) in
          let nrc3 := (nraenv_to_nnrc_ext op3 varid varenv) in
          let (t2,t3) := fresh_var2 "tprod$" "tprod$" (varid::varenv::nil) in
          NNRCUnop AFlatten
                       (NNRCFor t2 nrc2
                                    (NNRCFor t3 nrc3
                                                 ((NNRCBinop AConcat) (NNRCVar t2) (NNRCVar t3))))
      in
      let t := fresh_var "tsel$" (varid::varenv::nil) in
      let nrc1 := (nraenv_to_nnrc_ext op1 t varenv) in
      NNRCUnop AFlatten
              (NNRCFor t nrc2
                      (NNRCIf nrc1 (NNRCUnop AColl (NNRCVar t)) (NNRCConst (dcoll nil))))
    | NRAEnvProject sl op1 =>
      let t := fresh_var "tmap$" (varid::varenv::nil) in
      NNRCFor t (nraenv_to_nnrc_ext op1 varid varenv) (NNRCUnop (ARecProject sl) (NNRCVar t))
    | NRAEnvGroupBy g sl op1 =>
      NNRCGroupBy g sl (nraenv_to_nnrc_ext op1 varid varenv)
    end.

  Open Scope nraenv_scope.

  Lemma test op vid venv:
    nnrc_ext_to_nnrc (nraenv_to_nnrc_ext op vid venv)
    = algenv_to_nnrc (algenv_of_nraenv op) vid venv.
  Proof.
    revert vid venv; induction op; simpl; intros;
    try reflexivity;
    try (rewrite IHop1; rewrite IHop2; auto);
    try (rewrite IHop; auto);
    try (rewrite IHop3; reflexivity). (* join *)
    unfold nnrc_group_by.
    admit.
  Admitted.
  
  Lemma test2 h env op vid venv:
    nnrc_core_eval h env (nnrc_ext_to_nnrc (nraenv_to_nnrc_ext op vid venv))
    = nnrc_core_eval h env (algenv_to_nnrc (algenv_of_nraenv op) vid venv).
  Proof.
    revert vid venv env; induction op; intros;
    try reflexivity.
    - simpl; rewrite IHop1; rewrite IHop2; auto.
    - simpl; rewrite IHop; auto.
    - simpl. rewrite IHop2.
      destruct (nnrc_core_eval h env (algenv_to_nnrc (algenv_of_nraenv op2) vid venv));
        [|reflexivity].
      destruct d; simpl in *; try reflexivity.
      f_equal; apply rmap_ext; intros.
      rewrite IHop1; reflexivity.
    - simpl (nnrc_ext_to_nnrc
               (nraenv_to_nnrc_ext (NRAEnvMapConcat op1 op2) vid venv)).
      
      rewrite IHop2.
      destruct (nnrc_core_eval h env (algenv_to_nnrc (algenv_of_nraenv op2) vid venv));
        [|reflexivity].
      destruct d; simpl in *; try reflexivity.
      f_equal; apply rmap_ext; intros.
      rewrite IHop1; reflexivity.
    - 
      rewrite (map_sem_correct h op1 dcenv denv l); trivial.
      
    admit.
  Admitted.
  
  Theorem nraenv_sem_correct (h:list (string*string)) (op:nraenv) (env:bindings) (vid venv:var) dcenv (did denv:data) :
    prefix CONST_PREFIX vid = false ->
    prefix CONST_PREFIX venv = false ->
    vid <> venv ->
    (forall x,
        assoc_lookupr equiv_dec (mkConstants dcenv) x
        = lookup equiv_dec (filterConstants env) x) ->
    lookup equiv_dec env vid = Some did ->
    lookup equiv_dec env venv = Some denv ->
    @nnrc_ext_eval _ h env (nraenv_to_nnrc_ext op vid venv) = nraenv_eval h dcenv op denv did.
  Proof.
    intros.
    unfold nnrc_ext_eval.
    unfold nraenv_eval.
    rewrite test2.
    apply nraenv_sem_correct; assumption.
  Qed.

  Lemma nraenv_to_nnrc_ext_no_free_vars (op: algenv):
    forall (vid venv: var),
    forall v,
      In v (nrc_free_vars (nraenv_to_nnrc_ext op vid venv)) ->
      (prefix CONST_PREFIX v = true
      (* It is also true that: *)
      (* /\ In v (mkConstants (nraenv_constants op)) *)
      (* but stating this requires defining nraenv_constants *)
      )
      \/ v = vid \/ v = venv.
  Proof.
    algenv_cases (induction op) Case.
    - Case "NRAEnvID"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvConst"%string.
      contradiction.
    - Case "NRAEnvBinop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvUnop"%string.
      intros;
      simpl in *; repeat rewrite in_app_iff in *;
      intuition.
    - Case "NRAEnvMap"%string.
      intros vid venv v Hv.
      simpl in Hv.
      rewrite in_app_iff in Hv.
      destruct Hv.
      + auto.
      + apply remove_inv in H.
        destruct (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv v); intuition.
    - Case "NRAEnvMapConcat"%string.
      intros vid venv v.
      Opaque fresh_var2.
      simpl.
      case_eq (fresh_var2 "tmc$" "tmc$" (vid :: venv :: nil)); intros.
      simpl in *.
      rewrite in_app_iff in H0.
      elim H0; intros; clear H0.
      + apply IHop2; assumption.
      + destruct (string_eqdec s0 s0); try congruence.
        destruct (string_eqdec s0 s); try congruence; subst; clear e.
        * generalize (fresh_var2_distinct "tmc$" "tmc$" (vid :: venv :: nil)).
          rewrite H; simpl.
          congruence.
        * apply remove_inv in H1.
          elim H1; clear H1; intros.
          rewrite In_app_iff in H0; simpl in H0.
          elim H0; clear H0; intros; [congruence | ]. 
          clear IHop2.
          specialize (IHop1 s venv v H0).
          intuition.
    - Case "NRAEnvProduct"%string.
      intros vid venv v H.
      simpl in *.
      case_eq (fresh_var2 "tprod$" "tprod$" (vid :: venv :: nil)); intros.
      rewrite H0 in H. simpl in H.
      rewrite in_app_iff in H.
      destruct (string_eqdec s0 s0); try congruence.
      destruct (string_eqdec s0 s); try congruence; subst; clear e.
      + generalize (fresh_var2_distinct "tprod$" "tprod$" (vid :: venv :: nil)).
        rewrite H0; simpl.
        congruence.
      + elim H; clear H; intros.
        apply IHop1; assumption.
        apply remove_inv in H.
        elim H; clear H; intros.
      rewrite In_app_iff in H; simpl in H.
      elim H; clear H; intros. subst; congruence.
      apply IHop2; assumption.
    - Case "NRAEnvSelect"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv.
      + apply IHop2.
        assumption.
      + specialize (IHop1 ((fresh_var "tsel$" (vid :: venv :: nil))) venv v).
        clear IHop2.
        revert H IHop1.
        generalize (nrc_free_vars
                      (nraenv_to_nnrc_ext op1 (fresh_var "tsel$" (vid :: venv :: nil)) venv)).
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        intuition.
    - Case "NRAEnvDefault"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv.
      + apply IHop1.
        assumption.
      + match_destr_in H; [ | congruence].
        apply remove_inv in H.
        elim H; clear H; intros.
        rewrite In_app_iff in H; simpl in H.
        elim H; clear H; intros.
        subst; congruence.
        apply IHop2; assumption.
    - Case "NRAEnvEither"%string.
      intros vid venv v.
      simpl.
      match_case; intros ? ? eqq.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      destruct H.
      + apply remove_inv in H.
        elim H; clear H; intros.
        clear IHop2; specialize (IHop1 _ venv v H).
        intuition.
      + revert H.
        intros.
        apply remove_inv in H.
        elim H; clear H; intros.
        clear IHop1; specialize (IHop2 _ venv v H).
        intuition.
    - Case "NRAEnvEitherConcat"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      repeat rewrite in_app_iff in H.
      destruct H.
      destruct H as [?|[?|?]].
      + auto.
      + match_destr_in H; [| congruence ].
        match_destr_in H; simpl in *; intuition.
      + match_destr_in H; [| congruence ].
        match_destr_in H; simpl in *; intuition.
    - Case "NRAEnvApp"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 _ venv v H).
      intuition.
    - Case "NRAEnvGetConstant"%string.
      intros vid venv v.
      simpl.
      intros [?|?]; [|intuition].
      subst.
      left.
      simpl.
      rewrite prefix_nil.
      reflexivity.
    - Case "NRAEnvEnv"%string.
      intros vid venv v.
      simpl.
      intros Hv.
      intuition.
    - Case "NRAEnvAppEnv"%string.
      intros vid venv v.
      simpl.
      rewrite in_app_iff.
      intros Hv.
      destruct Hv; auto.
      apply remove_inv in H.
      destruct H.
      clear IHop2; specialize (IHop1 vid _ v H).
      intuition.
    - Case "NRAEnvMapEnv"%string.
      intros vid venv v.
      simpl.
      intros.
      elim H; clear H; intros; [ intuition | ].
      apply remove_inv in H.
      destruct H.
      specialize (IHop vid ((fresh_var "tmape$" (vid :: venv :: nil))) v H).
      intuition.
  Qed.

  Section Top.
    Definition nraenv_to_nnrc_ext_top (q:algenv) (init_vid init_venv:var) : nrc :=
      NNRCLet init_venv (NNRCConst (drec nil))
             (NNRCLet init_vid (NNRCConst dunit)
                     (nraenv_to_nnrc_ext q init_vid init_venv)).
  End Top.
  
  (** Lemma and proof of linear size translation *)

  Section size.

  Require Import Omega.

  Theorem algenvToNNNRC_size op vid venv : 
    nrc_size (nraenv_to_nnrc_ext op vid venv) <= 10 * algenv_size op.
  Proof.
    Transparent fresh_var2.
    revert vid venv.
    induction op; simpl in *; intros; trivial.
    - omega.
    - omega.
    - specialize (IHop1 vid venv); specialize (IHop2 vid venv); omega.
    - specialize (IHop vid venv); omega.
    - specialize (IHop1 (fresh_var "tmap$" (vid :: venv :: nil)) venv);
      specialize (IHop2 vid venv); omega.
    - repeat match_destr.
      specialize (IHop1 (fresh_var "tmc$" (vid :: venv :: nil)) venv); specialize (IHop2 vid venv); omega.
    - specialize (IHop1 vid venv); specialize (IHop2 vid venv); omega.
    - specialize (IHop1 (fresh_var "tsel$" (vid :: venv :: nil)) venv); specialize (IHop2 vid venv); omega.
    - specialize (IHop1 vid venv); specialize (IHop2 vid venv); omega.
    - specialize (IHop1 (fresh_var "teitherL$" (vid :: venv :: nil)) venv); specialize (IHop2 (fresh_var "teitherR$" (fresh_var "teitherL$" (vid :: venv :: nil) :: vid :: venv :: nil)) venv); omega.
    - specialize (IHop2 vid venv); specialize (IHop1 vid venv); omega.
    - specialize (IHop1 (fresh_var "tapp$" (vid :: venv :: nil)) venv); specialize (IHop2 vid venv); omega.
    - omega.
    - omega.
    - specialize (IHop1 vid (fresh_var "tappe$" (vid :: venv :: nil))); specialize (IHop2 vid venv); omega.
    - specialize (IHop vid (fresh_var "tmape$" (vid :: venv :: nil))); omega.
  Qed.

  End size.

End NRAEnvtoNNNRCExt.

(* 
*** Local Variables: ***
*** coq-load-path: (("../../coq" "Qcert")) ***
*** End: ***
*)
