From Stdlib Require Import
  Classes.Morphisms
  NArith.BinNat
  Relations.Relation_Definitions
  ZArith.BinInt.

From Stdlib Require Import ZArith.ZArith Strings.String.
Require Import stdpp.gmap.
From Stdlib Require Import Program.Equality.

From stdpp Require Import options.
From Stdlib Require Import Program.Basics.
Local Open Scope program_scope.
From stdpp Require Import
  gmap mapset option stringmap.

Import EqNotations.
Set Implicit Arguments.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Phoas Require Import programmingLanguage foas phoas hoas vcGen vcgWellFormed hoasSoundness vcgRelated.

(* Soundness of the verification condition generator: if the generated FOAS
   verification condition holds, the FOAS contract holds. The proof uses the
   relation between the HOAS and FOAS verification conditions from
   vcgRelated.v and the soundness of the HOAS one from hoasSoundness.v. *)

(* ------------------------------------------------------------------ *)
(* 1. Related HOAS and FOAS propositions are equivalent               *)
(* ------------------------------------------------------------------ *)

Lemma rel_exp_interp_to_va_crash (Γ : stringmap PL.Value) (v : PL.Value) (e : PL.Exp) :
  RelExp Γ v e -> PL.interp_to_va_crash PL.valueLogicVariable Γ e = Some v.
Proof.
  intro He.
  induction He; simpl; eauto.
  rewrite IHHe1, IHHe2. reflexivity.
Qed.

Lemma semant_hoas_foas_env (Γ : stringmap PL.Value) (hoas_prop : Hoas.prop) (foas_prop : Foas.prop) :
  RelHoasFoas Γ hoas_prop foas_prop ->
  (Hoas.semant hoas_prop <-> Foas.semant' Γ foas_prop).
Proof.
  intros Hrel.
  induction Hrel; simpl.
  - (* T *) reflexivity.
  - (* F *) reflexivity.
  - (* Implies *) rewrite IHHrel1, IHHrel2. reflexivity.
  - (* And *) rewrite IHHrel1, IHHrel2. reflexivity.
  - (* Or *) rewrite IHHrel1, IHHrel2. reflexivity.
  - (* Forall *) split; intros Hall v; apply H0, Hall.
  - (* Cmp *) rewrite (rel_exp_interp_to_va_crash H), (rel_exp_interp_to_va_crash H0). reflexivity.
Qed.

(* if a HOAS and FOAS proposition are related, then they are logically equivalent *)
Lemma semant_hoas_foas (hoas_prop : Hoas.prop) (foas_prop : Foas.prop) :
  RelHoasFoas ∅ hoas_prop foas_prop ->
  (Hoas.semant hoas_prop <-> Foas.semant foas_prop).
Proof.
  unfold Foas.semant.
  apply semant_hoas_foas_env.
Qed.



(* ------------------------------------------------------------------ *)
(* 2. Related HOAS and FOAS contracts                                 *)
(* ------------------------------------------------------------------ *)

(* A correspondence between a FOAS contract and the HOAS contract you get when
   translating it. Related contracts have the same semantics. *)
Inductive RelContract : Hoas.Contract -> Foas.Contract -> Prop :=
  | RelMkContract (forallVar arg result : string) (prog : PL.Prog)
      (pre_hoas : PL.Value -> Hoas.prop) (post_hoas : PL.Value -> PL.Value -> Hoas.prop)
      (pre_foas post_foas : Foas.prop) :
      (forall v, RelHoasFoas (<[forallVar := v]> ∅) (pre_hoas v) pre_foas) ->
      (forall v r, RelHoasFoas (<[result := r]> (<[forallVar := v]> ∅)) (post_hoas v r) post_foas) ->
      RelContract (Hoas.ForallC (fun v => Hoas.HoareTriple (pre_hoas v) prog v (post_hoas v)))
                  (Foas.MkContract forallVar pre_foas prog arg result post_foas).

Lemma rel_contract_semant (h : Hoas.Contract) (c : Foas.Contract) :
  RelContract h c -> Hoas.contract_semant h -> Foas.contract_semant c.
Proof.
  intros Hrel Hhoas.
  destruct Hrel as [forallVar arg result prog pre_hoas post_hoas pre_foas post_foas Hpre Hpost].
  intros forallVar' pre' prog' arg' result' post' Heq inp res Hpre_foas Harg Heval.
  injection Heq as <- <- <- <- <- <-.
  subst arg.
  specialize (Hpre inp).
  specialize (Hpost inp res).
  apply (semant_hoas_foas_env Hpost).
  apply (semant_hoas_foas_env Hpre) in Hpre_foas.
  unfold Hoas.contract_semant in Hhoas.
  apply (Hhoas pre_hoas prog post_hoas eq_refl inp res); assumption.
Qed.

Lemma rel_exp_interp_to_va_default (store : stringmap PL.Value) (e : PL.Exp)
  (He : WfExp (dom store) e) :
  RelExp store (PL.interp_to_va_default PL.valueLogicVariable store e) e.
Proof.
  induction He; simpl.
  - constructor.
  - apply elem_of_dom in H.
    destruct H as [v Hv].
    rewrite Hv.
    constructor. exact Hv.
  - constructor; assumption.
Qed.

Lemma rel_foas_to_hoas (store : stringmap PL.Value) (p : Foas.prop) :
  Foas_wf.WfProp (dom store) p ->
  RelHoasFoas store (Hoas.phoas_to_hoas (Phoas.foas_to_phoas PL.valueLogicVariable store p)) p.
Proof.
  revert store.
  induction p; intros store Hp; simpl; constructor; inversion Hp; subst.
  - apply rel_exp_interp_to_va_default; assumption.
  - apply rel_exp_interp_to_va_default; assumption.
  - apply IHp1; assumption.
  - apply IHp2; assumption.
  - apply IHp1; assumption.
  - apply IHp2; assumption.
  - apply IHp1; assumption.
  - apply IHp2; assumption.
  - intros v.
    apply IHp.
    rewrite dom_insert_L, union_comm_L.
    assumption.
Qed.

Lemma rel_contract_foas_to_hoas (c : Foas.Contract) (Hc : Foas_wf.WfContract c) :
  RelContract (Hoas.foas_contract_to_hoas_contract c) c.
Proof.
  destruct c as [forallVar pre prog arg result post].
  destruct Hc as [Hpre [Harg [Hneq Hpost]]].
  simpl.
  constructor; intros.
  - apply rel_foas_to_hoas.
    rewrite dom_singleton_L.
    assumption.
  - (* the store of the postcondition, written as a union of singletons *)
    assert (Heq : <[result := r]> (<[forallVar := v]> (∅ : stringmap PL.Value))
                  = {[forallVar := v]} ∪ {[result := r]}).
    { rewrite insert_empty.
      rewrite <- insert_union_singleton_r.
      - reflexivity.
      - apply lookup_singleton_ne. exact Hneq. }
    rewrite Heq.
    apply rel_foas_to_hoas.
    rewrite dom_union_L, !dom_singleton_L.
    assumption.
Qed.

(* translating a FOAS contract to a HOAS contract preserves its semantics *)
Lemma contract_translation_preserves_semantics (c : Foas.Contract) (Hc : Foas_wf.WfContract c) :
  Hoas.contract_semant (Hoas.foas_contract_to_hoas_contract c) -> Foas.contract_semant c.
Proof.
  apply rel_contract_semant.
  apply rel_contract_foas_to_hoas.
  exact Hc.
Qed.



(* ------------------------------------------------------------------ *)
(* 3. Adequacy of the generated verification conditions               *)
(* ------------------------------------------------------------------ *)

(* when the HOAS verification condition holds, the FOAS contract holds *)
Theorem hoas_adequate (c : Foas.Contract) (Hc : Foas_wf.WfContract c) :
  Hoas.semant (vcg.vc_hoas c) -> Foas.contract_semant c.
Proof.
  intros Hvc.
  rewrite vcg.vc_hoas_unfold in Hvc.
  apply contract_translation_preserves_semantics; [exact Hc |].
  apply adequate. exact Hvc.
Qed.

(* If the verification condition is true, running the program with the right
   precondition will yield a result with the right postcondition. *)
Theorem foas_adequate (c : Foas.Contract) (Hc : Foas_wf.WfContract c) :
  Foas.semant (vcg.vc_foas c) -> Foas.contract_semant c.
Proof.
  intros Hvc.
  apply hoas_adequate; [exact Hc |].
  apply (semant_hoas_foas (rel_vc_hoas_foas c)).
  exact Hvc.
Qed.
