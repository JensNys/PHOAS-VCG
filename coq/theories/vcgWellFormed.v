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

From Phoas Require Import programmingLanguage foas phoas hoas vcGen.

(* Well-formedness (well-scopedness) of the verification condition generator.
   This file mirrors vcgRelated.v: every [WfX]/[wf_x] here has a binary
   counterpart [RelX]/[rel_x] there, in the same order.

   Naming conventions:
   - predicates of type [WF World X] (and their type classes) are CamelCase
     and start with [Wf];
   - lemmas are snake_case and start with [wf_], followed by the name of the
     function they are about (e.g. [wf_lookupWstore] is about [lookupWstore]);
   - hypotheses are named [H...], e.g. [Hacc], [Hpost], [Hstore]. *)



(* ================================================================== *)
(* Part 1: Kripke-style well-formedness, independent of the object language *)
(* ================================================================== *)

(* A well-formedness predicate on [X], indexed by worlds. *)
Definition WF (World : Set) (X : Set) := World -> X -> Prop.

(* Well-formedness is preserved when moving to a larger world. *)
Class WfWeakening {World X : Set} (acc : relation World) (wf_X : WF World X) := {
  wf_weaken : forall (w w' : World) (x : X), acc w w' -> wf_X w x -> wf_X w' x
}.

Section Kripke.
  Context {World : Set} (acc : relation World).

  (* functions map well-formed arguments to well-formed results *)
  Definition WfFunc {A B : Set} (wf_A : WF World A) (wf_B : WF World B) : WF World (A -> B) :=
    fun w f => forall (a : A), wf_A w a -> wf_B w (f a).

  (* well-formed in every larger world *)
  Definition WfBox {A : Set} (wf_A : WF World A) : WF World A :=
    fun w a => forall w', acc w w' -> wf_A w' a.

  Definition WfUnit : WF World unit :=
    fun w u => True.

  Inductive WfOption {A : Set} (wf_A : WF World A) (w : World) : option A -> Prop :=
    | WfNone : WfOption wf_A w None
    | WfSome (a : A) : wf_A w a -> WfOption wf_A w (Some a).

  Lemma wf_option_weaken {A : Set} (wf_A : WF World A) (Hweaken : WfWeakening acc wf_A)
    (w w' : World) (o : option A) :
    acc w w' -> WfOption wf_A w o -> WfOption wf_A w' o.
  Proof.
    intros Hacc Ho.
    destruct Ho; constructor.
    eapply wf_weaken; eauto.
  Qed.

End Kripke.

Declare Scope wf_scope.
Delimit Scope wf_scope with wf.
Notation "A ↣ B" := (WfFunc A%wf B%wf)
  (at level 99, B at level 200, right associativity) : wf_scope.
Local Open Scope wf_scope.



(* ================================================================== *)
(* Part 2: Well-formedness of PHOAS propositions                       *)
(* ================================================================== *)

Section Props.
  Context {World : Set} (acc : relation World).
  Variable (A : Set) (wf_A : WF World A).

  Inductive WfProp (w : World) : Phoas.prop A -> Prop :=
    | WfT : WfProp w (Phoas.T A)
    | WfF : WfProp w (Phoas.F A)
    | WfImplies {l r : Phoas.prop A} :
        WfProp w l -> WfProp w r -> WfProp w (Phoas.Implies l r)
    | WfAnd {l r : Phoas.prop A} :
        WfProp w l -> WfProp w r -> WfProp w (Phoas.And l r)
    | WfOr {l r : Phoas.prop A} :
        WfProp w l -> WfProp w r -> WfProp w (Phoas.Or l r)
    | WfForall {f : A -> Phoas.prop A} :
        (forall (a : A) w', acc w w' -> wf_A w' a -> WfProp w' (f a)) ->
        WfProp w (Phoas.Forall f)
    | WfCmp {r : Relop} {a b : A} :
        wf_A w a -> wf_A w b -> WfProp w (Phoas.Cmp r a b).

End Props.



(* ================================================================== *)
(* Part 3: Object-language specific well-formedness                    *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* 3.1 Logic variables and stores                                      *)
(* ------------------------------------------------------------------ *)

(* the operations of a logic variable preserve well-formedness *)
Class WfLogicVariable {World V : Set} (LV : PL.LogicVariable V) (wf_V : WF World V) := {
  wf_lit : forall w n, wf_V w (LV.(PL.lit) n);
  wf_add : forall w a b, wf_V w a -> wf_V w b -> wf_V w (LV.(PL.add) a b)
}.

(* every variable in the store is bound to a well-formed value *)
Definition WfStore {World V : Set} (wf_V : WF World V) : WF World (stringmap V) :=
  fun w store => forall x, WfOption wf_V w (store !! x).



(* ------------------------------------------------------------------ *)
(* 3.2 Concrete worlds: sets of variables in scope                     *)
(* ------------------------------------------------------------------ *)

(* expressions whose variables are in scope *)
Definition WfExp : WF stringset PL.Exp :=
  fun Γ e => PL.wfexp Γ e.

(* A reader is well-formed in Γ if it produces a well-formed expression in
   every larger scope. Quantifying over all larger scopes makes [WfReader]
   closed under weakening (a reader may compute something different in a
   larger scope). *)
Definition WfReader : WF stringset (Phoas.R PL.Exp) :=
  fun Γ m => forall Γ', Γ ⊆ Γ' -> WfExp Γ' (m Γ').

Lemma wf_lit_exp (Γ : stringset) (n : PL.Value) :
  WfExp Γ (PL.expLogicVariable.(PL.lit) n).
Proof.
  constructor.
Qed.

Lemma wf_add_exp (Γ : stringset) (a b : PL.Exp) :
  WfExp Γ a -> WfExp Γ b -> WfExp Γ (PL.expLogicVariable.(PL.add) a b).
Proof.
  intros Ha Hb.
  constructor; assumption.
Qed.

#[export] Instance wf_lv_exp : WfLogicVariable PL.expLogicVariable WfExp := {
  wf_lit := wf_lit_exp;
  wf_add := wf_add_exp
}.

Lemma wf_weaken_exp (Γ Γ' : stringset) (e : PL.Exp) :
  Γ ⊆ Γ' -> WfExp Γ e -> WfExp Γ' e.
Proof.
  intros Hsub He.
  induction He.
  - constructor.
  - constructor. set_solver.
  - constructor; assumption.
Qed.

#[export] Instance wf_weakening_exp : WfWeakening subseteq WfExp := {
  wf_weaken := wf_weaken_exp
}.

Lemma wf_lit_reader (Γ : stringset) (n : PL.Value) :
  WfReader Γ (Phoas.R_logicVariable.(PL.lit) n).
Proof.
  intros Γ' Hsub.
  constructor.
Qed.

Lemma wf_add_reader (Γ : stringset) (a b : Phoas.R PL.Exp) :
  WfReader Γ a -> WfReader Γ b -> WfReader Γ (Phoas.R_logicVariable.(PL.add) a b).
Proof.
  intros Ha Hb Γ' Hsub.
  constructor; [apply Ha | apply Hb]; exact Hsub.
Qed.

#[export] Instance wf_lv_reader : WfLogicVariable Phoas.R_logicVariable WfReader := {
  wf_lit := wf_lit_reader;
  wf_add := wf_add_reader
}.

(* [WfReader] is closed under weakening by construction *)
Lemma wf_weaken_reader (Γ Γ' : stringset) (m : Phoas.R PL.Exp) :
  Γ ⊆ Γ' -> WfReader Γ m -> WfReader Γ' m.
Proof.
  intros Hsub Hm Γ'' Hsub'.
  apply Hm. etransitivity; eassumption.
Qed.

#[export] Instance wf_weakening_reader : WfWeakening subseteq WfReader := {
  wf_weaken := wf_weaken_reader
}.



(* ------------------------------------------------------------------ *)
(* 3.3 FOAS propositions and contracts                                 *)
(* ------------------------------------------------------------------ *)

Module Foas_wf.

  Inductive WfProp (Γ : stringset) : Foas.prop -> Prop :=
    | WfT : WfProp Γ Foas.T
    | WfF : WfProp Γ Foas.F
    | WfCmp r a b : WfExp Γ a -> WfExp Γ b -> WfProp Γ (Foas.Cmp r a b)
    | WfImplies l r : WfProp Γ l -> WfProp Γ r -> WfProp Γ (Foas.Implies l r)
    | WfAnd l r : WfProp Γ l -> WfProp Γ r -> WfProp Γ (Foas.And l r)
    | WfOr l r : WfProp Γ l -> WfProp Γ r -> WfProp Γ (Foas.Or l r)
    | WfForall (x : string) (body : Foas.prop) :
        WfProp (Γ ∪ {[x]}) body -> WfProp Γ (Foas.Forall x body).

  Definition WfContract (c : Foas.Contract) : Prop :=
    match c with
    | Foas.MkContract forallVar pre prog arg result post =>
        WfProp {[forallVar]} pre /\
        forallVar = arg /\
        forallVar <> result /\
        WfProp ({[forallVar]} ∪ {[result]}) post
    end.

End Foas_wf.



(* ------------------------------------------------------------------ *)
(* 3.4 Translation from FOAS and the verification condition generator  *)
(* ------------------------------------------------------------------ *)

Section Vcg.
  Variable (World : Set) (acc : relation World) (Hpreorder : PreOrder acc).
  Variable (V : Set) (wf_V : WF World V) (LV : PL.LogicVariable V).
  Variable (HLV : WfLogicVariable LV wf_V) (Hweaken : WfWeakening acc wf_V).

  (* worlds only grow: [acc] is reflexive and transitive *)
  #[local] Hint Extern 1 (acc _ _) => reflexivity : core.
  #[local] Hint Extern 2 (acc _ _) => (etransitivity; eassumption) : core.

  Notation "□ A" := (WfBox acc A%wf) (at level 50, A at level 9) : wf_scope.

  (* stores *)

  Lemma wf_store_weaken (w w' : World) (store : stringmap V) :
    acc w w' -> WfStore wf_V w store -> WfStore wf_V w' store.
  Proof using Hweaken V World acc wf_V.
    intros Hacc Hstore x.
    eapply wf_option_weaken; eauto.
  Qed.

  Lemma wf_store_singleton (w : World) (x : string) (v : V) :
    wf_V w v -> WfStore wf_V w {[x := v]}.
  Proof.
    intros Hv y.
    destruct (decide (y = x)) as [-> | Hne].
    - rewrite !lookup_singleton_eq. constructor. exact Hv.
    - rewrite !lookup_singleton_ne by congruence. constructor.
  Qed.

  Lemma wf_store_insert (w : World) (x : string) (v : V) (store : stringmap V) :
    wf_V w v -> WfStore wf_V w store -> WfStore wf_V w (<[x := v]> store).
  Proof.
    intros Hv Hstore y.
    destruct (decide (y = x)) as [-> | Hne].
    - rewrite !lookup_insert_eq. constructor. exact Hv.
    - rewrite !lookup_insert_ne by congruence. apply Hstore.
  Qed.

  Lemma wf_store_delete (w : World) (x : string) (store : stringmap V) :
    WfStore wf_V w store -> WfStore wf_V w (delete x store).
  Proof.
    intros Hstore y.
    destruct (decide (y = x)) as [-> | Hne].
    - rewrite !lookup_delete_eq. constructor.
    - rewrite !lookup_delete_ne by congruence. apply Hstore.
  Qed.

  Lemma wf_store_union (w : World) (store store' : stringmap V) :
    WfStore wf_V w store -> WfStore wf_V w store' -> WfStore wf_V w (store ∪ store').
  Proof.
    intros Hstore Hstore' x.
    rewrite !lookup_union.
    destruct (Hstore x); destruct (Hstore' x); constructor; assumption.
  Qed.

  (* translation from FOAS *)

  Lemma wf_interp_to_va_default (e : PL.Exp) (w : World) (store : stringmap V)
    (Hstore : WfStore wf_V w store) :
    wf_V w (PL.interp_to_va_default LV store e).
  Proof using HLV LV V World wf_V.
    induction e; simpl.
    - apply wf_lit.
    - (* if x is in the store, its value is well-formed; otherwise we default to lit 0 *)
      destruct (Hstore x); [apply wf_lit | assumption].
    - apply wf_add; assumption.
  Qed.

  Lemma wf_interp_to_va_crash (e : PL.Exp) (w : World) (store : stringmap V)
    (Hstore : WfStore wf_V w store) :
    WfOption wf_V w (PL.interp_to_va_crash LV store e).
  Proof using HLV LV V World wf_V.
    induction e; simpl.
    - constructor. apply wf_lit.
    - apply Hstore.
    - destruct IHe1; [constructor |].
      destruct IHe2; [constructor |].
      constructor. apply wf_add; assumption.
  Qed.

  Lemma wf_foas_to_phoas (p : Foas.prop) (w : World) (store : stringmap V)
    (Hstore : WfStore wf_V w store) :
    WfProp acc wf_V w (Phoas.foas_to_phoas LV store p).
  Proof using HLV Hweaken LV V World acc wf_V.
    revert w store Hstore.
    induction p; intros w store Hstore; simpl.
    - constructor.
    - constructor.
    - constructor; apply wf_interp_to_va_default; exact Hstore.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.
      intros v w1 Hacc1 Hv.
      apply IHp.
      apply wf_store_insert; [exact Hv |].
      eapply wf_store_weaken; eauto.
  Qed.

  (* the store monad *)

  Definition WfPost {A : Set} (wf_A : WF World A) : WF World (A -> stringmap V -> Phoas.prop V) :=
    wf_A ↣ WfStore wf_V ↣ WfProp acc wf_V.

  Definition WfWstore {A : Set} (wf_A : WF World A) : WF World (vcg.Wstore V A) :=
    (□ (WfPost wf_A)) ↣ WfStore wf_V ↣ WfProp acc wf_V.

  Definition WfLift {A B : Set} (wf_A : WF World A) (wf_B : WF World B) : WF World (A -> vcg.Wstore V B) :=
    wf_A ↣ WfWstore wf_B.

  Lemma wf_ret {A : Set} (wf_A : WF World A) (w : World) (a : A) (Ha : wf_A w a) :
    WfWstore wf_A w (vcg.ret a).
  Proof using Hpreorder V World acc wf_V.
    intros post Hpost store Hstore.
    eapply Hpost; eauto.
  Qed.

  Lemma wf_bind {A B : Set} (wf_A : WF World A) (wf_B : WF World B) (w : World)
    (m : vcg.Wstore V A) (k : A -> vcg.Wstore V B)
    (Hm : WfWstore wf_A w m) (Hk : (□ (WfLift wf_A wf_B)) w k) :
    WfWstore wf_B w (vcg.bind m k).
  Proof using Hpreorder V World acc wf_V.
    unfold vcg.bind, WfWstore, WfLift, WfPost, WfFunc, WfBox in *.
    intros post Hpost store Hstore.
    (* first run m, ... *)
    apply Hm; [| exact Hstore].
    intros w1 Hacc1 a Ha store1 Hstore1.
    (* ... then run k on its result *)
    apply (Hk w1 Hacc1 a Ha); [| exact Hstore1].
    intros w2 Hacc2 b Hb store2 Hstore2.
    apply Hpost; [etransitivity; eassumption | exact Hb | exact Hstore2].
  Qed.

  Lemma wf_lookupWstore (w : World) (x : string) :
    WfWstore wf_V w (vcg.lookupWstore x).
  Proof using Hpreorder V World acc wf_V.
    unfold vcg.lookupWstore.
    intros post Hpost store Hstore.
    destruct (Hstore x).
    - constructor.
    - apply Hpost; eauto.
  Qed.

  Lemma wf_lookupWstore_safe (w : World) (x : string) :
    WfWstore (WfOption wf_V) w (vcg.lookupWstore_safe x).
  Proof using Hpreorder V World acc wf_V.
    unfold vcg.lookupWstore_safe.
    intros post Hpost store Hstore.
    apply Hpost; eauto.
  Qed.

  Lemma wf_insertWstore (w : World) (x : string) (v : V) (Hv : wf_V w v) :
    WfWstore WfUnit w (vcg.insertWstore x v).
  Proof using Hpreorder V World acc wf_V.
    unfold vcg.insertWstore.
    intros post Hpost store Hstore.
    apply (Hpost w ltac:(reflexivity) tt I).
    apply wf_store_insert; assumption.
  Qed.

  Lemma wf_deleteWstore (w : World) (x : string) :
    WfWstore WfUnit w (vcg.deleteWstore x).
  Proof using Hpreorder V World acc wf_V.
    unfold vcg.deleteWstore.
    intros post Hpost store Hstore.
    apply (Hpost w ltac:(reflexivity) tt I).
    apply wf_store_delete; assumption.
  Qed.

  Lemma wf_restoreWstore (w : World) (x : string) (o : option V) (Ho : WfOption wf_V w o) :
    WfWstore WfUnit w (vcg.restoreWstore x o).
  Proof using Hpreorder V World acc wf_V.
    destruct Ho; simpl.
    - apply wf_deleteWstore.
    - apply wf_insertWstore; assumption.
  Qed.

  (* the verification condition generator *)

  Lemma wf_exec_exp (e : PL.Exp) (w : World) :
    WfWstore wf_V w (vcg.exec_exp LV e).
  Proof using HLV Hpreorder Hweaken LV V World acc wf_V.
    revert w.
    induction e; intros w post Hpost store Hstore.
    - (* Lit *)
      simpl. eapply Hpost; eauto.
      apply wf_lit.
    - (* Var *)
      simpl. eapply wf_lookupWstore; eauto.
    - (* Add *)
      simpl. eapply wf_bind; eauto.
      intros w1 Hacc1 a Ha.
      eapply wf_bind with (wf_A := wf_V).
      + apply IHe2.
      + intros w2 Hacc2 b Hb.
        eapply wf_ret.
        apply wf_add.
        * eapply wf_weaken; eauto.
        * exact Hb.
  Qed.

  Lemma wf_exec_stm (stm : PL.Stm) (w : World) :
    WfWstore wf_V w (vcg.exec_stm LV stm).
  Proof using HLV Hpreorder Hweaken LV V World acc wf_V.
    revert w.
    induction stm; intros w; simpl.
    - apply wf_exec_exp.
    - eapply wf_bind.
      + apply wf_exec_exp.
      + intros w1 Hacc1 v Hv.
        eapply wf_bind.
        * apply wf_lookupWstore_safe.
        * intros w2 Hacc2 previous Hprevious.
          eapply wf_bind.
          -- apply wf_insertWstore. eapply wf_weaken; eauto.
          -- intros w3 Hacc3 _ _.
             eapply wf_bind.
             ++ apply IHstm.
             ++ intros w4 Hacc4 result Hresult.
                eapply wf_bind.
                ** apply wf_restoreWstore.
                   eapply (wf_option_weaken Hweaken); [| exact Hprevious]. eauto.
                ** intros w5 Hacc5 _ _.
                   eapply wf_ret.
                   eapply wf_weaken; eauto.
  Qed.

  Lemma wf_wp (stm : PL.Stm) (w : World)
    (post : V -> stringmap V -> Phoas.prop V) (store : stringmap V)
    (Hpost : (□ (WfPost wf_V)) w post) (Hstore : WfStore wf_V w store) :
    WfProp acc wf_V w (vcg.wp LV stm post store).
  Proof using HLV Hpreorder Hweaken LV V World acc wf_V.
    unfold vcg.wp.
    eapply wf_exec_stm; eauto.
  Qed.

  Lemma wf_vc (c : Foas.Contract) (w : World) :
    WfProp acc wf_V w (vcg.vc LV c).
  Proof using HLV Hpreorder Hweaken LV V World acc wf_V.
    destruct c as [forallVar pre prog arg result post].
    destruct prog as [functionName param body].
    simpl.
    (* the logic variable of the contract *)
    constructor.
    intros v w1 Hacc1 Hv.
    constructor.
    - (* precondition *)
      apply wf_foas_to_phoas.
      apply wf_store_singleton. exact Hv.
    - (* weakest precondition of the body *)
      apply wf_wp.
      + (* postcondition: the forall variable and the result are in scope *)
        intros w2 Hacc2 result_v Hresult store Hstore.
        unfold vcg.ignore_map.
        apply wf_foas_to_phoas.
        apply wf_store_union; apply wf_store_singleton.
        * eapply wf_weaken; eauto.
        * exact Hresult.
      + (* initial store *)
        apply wf_store_singleton. exact Hv.
  Qed.

End Vcg.



(* ------------------------------------------------------------------ *)
(* 3.5 Translation to FOAS                                             *)
(* ------------------------------------------------------------------ *)

Lemma wf_phoas_to_foas (Γ : stringset) (p : Phoas.prop (Phoas.R PL.Exp))
  (Hp : WfProp subseteq WfReader Γ p) :
  Foas_wf.WfProp Γ (Phoas.phoas_to_foas Γ p).
Proof.
  induction Hp; cbn.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - (* the fresh variable is in scope in the body *)
    constructor.
    apply H0.
    + set_solver.
    + intros Γ' Hsub. constructor. set_solver.
  - (* run both readers in the current scope *)
    constructor; [apply H | apply H0]; reflexivity.
Qed.



(* ------------------------------------------------------------------ *)
(* 3.6 The generated verification condition is well-formed            *)
(* ------------------------------------------------------------------ *)

Theorem wf_vc_foas (c : Foas.Contract) : Foas_wf.WfProp ∅ (vcg.vc_foas c).
Proof.
  eapply wf_phoas_to_foas.
  apply (wf_vc set_subseteq_preorder wf_lv_reader wf_weakening_reader).
Qed.

(* All PHOAS propositions are well-formed (meta-theoretical result that is not provable) *)
Lemma wf_all_phoas (World V : Set) (wf_V : WF World V) (acc : relation World)
  (w : World) (p : Phoas.prop V) :
  WfProp acc wf_V w p.
Proof.
Admitted.

(* the same statement, this time proven using the meta-theoretical result *)
Theorem wf_vc_foas' (c : Foas.Contract) : Foas_wf.WfProp ∅ (vcg.vc_foas c).
Proof.
  eapply wf_phoas_to_foas.
  eapply wf_all_phoas.
Qed.
