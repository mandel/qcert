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

Require Import CompilerRuntime.
Module CompCore(runtime:CompilerRuntime).

  Require Import String List String EquivDec.
  Require Import BasicRuntime.
  Require Import Pattern Rule.
  Require Import CompUtil.
  Require Import NRAEnvRuntime.
  Require Import NNRCRuntime NNRCMRRuntime.
  Require Import NRAEnvtoNNRC NRewFunc.
  Require Import NNRCtoNNRCMR NRewMR .

  Require Import CompDriver.
  Module CD := CompDriver runtime.
  
  (* Compiler from NRAEnv to NNRC *)

  (* Java equivalent: NraToNnrc.convert *)
  Definition translate_nraenv_to_nnrc (q:CD.nraenv) : CD.nnrc :=
    CD.nraenv_to_nnrc q.

  Require Import TOptimEnvFunc.

  (**********************
   * Typed NNRC Section *
   **********************)

  Require Import NNRCTypes.
  Require Import TNRAEnvtoNNRC.
  Require Import TRewFunc.

  (* Typed compilation from NRAEnv to NNRC *)

  Definition tcompile_nraenv_to_nnrc_typed_opt (q:CD.nraenv) : CD.nnrc :=
    let op_optim := toptim_nraenv q in
    let e_init := translate_nraenv_to_nnrc op_optim in
    let e_rew := trew e_init in
    e_rew.

  Definition trew_nnrc_typed_opt (q:CD.nnrc) : CD.nnrc :=
    trew q.

  (***********************
   * Typed DNNRC Section *
   ***********************)

  Require Import DData DNNRC NNRCtoDNNRC SparkIR.

  (* Typed compilation from NRAEnv to DNNRC *)

  Definition translate_nnrc_to_dnnrc
             (tenv:list(var*dlocalization)) (e_nrc:nrc) : CD.dnnrc_dataset :=
    nrc_to_dnrc tt tenv e_nrc.

  Definition tcompile_nraenv_to_dnnrc (q:CD.nraenv) : CD.dnnrc_dataset :=
    CD.nnrc_to_dnnrc_dataset (CD.nnrc_optim (CD.nraenv_to_nnrc (CD.nraenv_optim q))).

  Require Import TDNRCInfer DNNRCtoScala DNNRCSparkIRRewrites.

  Definition dnnrc_to_typeannotated_dnnrc
             {bm:brand_model}
             {ftyping: foreign_typing}
             (e: dnrc _ unit dataset) (inputType: rtype)
    : option (dnrc _ (type_annotation unit) dataset) :=
    dnnrc_infer_type e inputType.

  (******************
   * NNRCMR Section *
   ******************)

  (* - For now the assumption is that all free vars in the original nrc
       expression are collections and will be distributed.
     - The free variables are obtained after nrc rewrites
     - one has to be careful to pass those free variables to the mr-optimizer *)

  (* Java equivalent: NnrcToNrcmr.convert *)
  Definition translate_nnrc_to_nnrcmr_chain (e_nrc:nrc) :=
    let e_nrc_no_id := nrc_subst e_nrc init_vid (NRCConst dunit) in
    let e_rew := trew e_nrc_no_id in
    let e_rew_free_vars := (* bdistinct !!! *) nrc_free_vars e_rew in
    let env_variables :=
        (init_vid, Vlocal)
          ::(init_vinit, Vlocal)
          ::(localize_names e_rew_free_vars)
    in
    let e_mr :=
        nnrc_to_nnrcmr_chain e_rew
                             init_vinit
                             env_variables
    in
    e_mr.

  Definition tcompile_nraenv_to_nnrcmr_chain_no_optim (op_init:algenv) : nrcmr :=
    let e_nrc := tcompile_nraenv_to_nnrc_typed_opt op_init in
    translate_nnrc_to_nnrcmr_chain e_nrc.

  Definition tcompile_nnrc_to_nnrcmr_chain_typed_opt (e_nrc:nrc) : nrcmr :=
    let e_mr := translate_nnrc_to_nnrcmr_chain e_nrc in
    let e_mr_optim := mr_optimize e_mr in
    e_mr_optim.

  Definition tcompile_nraenv_to_nnrcmr_chain_typed_opt (op_init:algenv) : nrcmr :=
    let e_mr := tcompile_nraenv_to_nnrcmr_chain_no_optim op_init in
    let e_mr_optim := mr_optimize e_mr in
    e_mr_optim.

  (* Some utilities... *)
  (* XXX Should be lifted in a different module for extraction ? XXX *)

  (* HACK: mr_reduce_empty isn't a field of mr so it needs to be exposed *)
  Definition mr_reduce_empty := mr_reduce_empty.

  (* Access to type annotations *)
  Definition type_annotation {br:brand_relation} (A:Set): Set
    := TDNRCInfer.type_annotation A.

  Definition ta_base {br:brand_relation} (A:Set) (ta:type_annotation A)
    := TDNRCInfer.ta_base ta.
  Definition ta_inferred {br:brand_relation} (A:Set) (ta:type_annotation A)
    := TDNRCInfer.ta_inferred ta .
  Definition ta_required {br:brand_relation} (A:Set) (ta:type_annotation A)
    := TDNRCInfer.ta_required ta.
  
End CompCore.

(*
*** Local Variables: ***
*** coq-load-path: (("../../../coq" "QCert")) ***
*** End: ***
*)
