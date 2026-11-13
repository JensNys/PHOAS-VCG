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

From Phoas Require Import programmingLanguage foas phoas hoas vcGen vcgWellFormed.

(* Binary logical relations for the verification condition generator: running
   it on related logic variables gives related results.
   This file mirrors vcgWellFormed.v: every [RelX]/[rel_x] here has a unary
   counterpart [WfX]/[wf_x] there, in the same order. vcgSoundness.v uses
   the relations to prove the generator sound.

   Naming conventions:
   - relations of type [Related World X1 X2] (and their type classes) are
     CamelCase and start with [Rel];
   - lemmas are snake_case and start with [rel_], followed by the name of the
     function they are about (e.g. [rel_lookupWstore] is about [lookupWstore]);
   - hypotheses are named [H...], e.g. [Hacc], [Hpost], [Hstore]. *)



(* ================================================================== *)
(* Part 1: Kripke-style relations, independent of the object language  *)
(* ================================================================== *)

(* A relation between [X1] and [X2], indexed by worlds. *)
Definition Related (World : Set) (X1 X2 : Set) := World -> X1 -> X2 -> Prop.

(* Related values stay related when moving to a larger world. *)
Class RelWeakening {World X1 X2 : Set} (acc : relation World) (rel_X : Related World X1 X2) := {
  rel_weaken : forall (w w' : World) (x1 : X1) (x2 : X2), acc w w' -> rel_X w x1 x2 -> rel_X w' x1 x2
}.

Section Kripke.
  Context {World : Set} (acc : relation World).

  (* functions map related arguments to related results *)
  Definition RelFunc {A1 A2 B1 B2 : Set} (rel_A : Related World A1 A2) (rel_B : Related World B1 B2) :
    Related World (A1 -> B1) (A2 -> B2) :=
    fun w f1 f2 => forall (a1 : A1) (a2 : A2), rel_A w a1 a2 -> rel_B w (f1 a1) (f2 a2).

  (* related in every larger world *)
  Definition RelBox {A1 A2 : Set} (rel_A : Related World A1 A2) : Related World A1 A2 :=
    fun w a1 a2 => forall w', acc w w' -> rel_A w' a1 a2.

  Definition RelUnit : Related World unit unit :=
    fun w u1 u2 => True.

  Inductive RelOption {A1 A2 : Set} (rel_A : Related World A1 A2) (w : World) : option A1 -> option A2 -> Prop :=
    | RelNone : RelOption rel_A w None None
    | RelSome (a1 : A1) (a2 : A2) : rel_A w a1 a2 -> RelOption rel_A w (Some a1) (Some a2).

  Lemma rel_option_weaken {A1 A2 : Set} (rel_A : Related World A1 A2) (Hweaken : RelWeakening acc rel_A)
    (w w' : World) (o1 : option A1) (o2 : option A2) :
    acc w w' -> RelOption rel_A w o1 o2 -> RelOption rel_A w' o1 o2.
  Proof.
    intros Hacc Ho.
    destruct Ho; constructor.
    eapply rel_weaken; eauto.
  Qed.

End Kripke.

Declare Scope rel_scope.
Delimit Scope rel_scope with rel.
Notation "A ↣ B" := (RelFunc A%rel B%rel)
  (at level 99, B at level 200, right associativity) : rel_scope.
Local Open Scope rel_scope.



(* ================================================================== *)
(* Part 2: Related PHOAS propositions                                  *)
(* ================================================================== *)

Section Props.
  Context {World : Set} (acc : relation World).
  Variable (A1 A2 : Set) (rel_A : Related World A1 A2).

  Inductive RelProp (w : World) : Phoas.prop A1 -> Phoas.prop A2 -> Prop :=
    | RelT : RelProp w (Phoas.T A1) (Phoas.T A2)
    | RelF : RelProp w (Phoas.F A1) (Phoas.F A2)
    | RelImplies {l1 r1 : Phoas.prop A1} {l2 r2 : Phoas.prop A2} :
        RelProp w l1 l2 -> RelProp w r1 r2 -> RelProp w (Phoas.Implies l1 r1) (Phoas.Implies l2 r2)
    | RelAnd {l1 r1 : Phoas.prop A1} {l2 r2 : Phoas.prop A2} :
        RelProp w l1 l2 -> RelProp w r1 r2 -> RelProp w (Phoas.And l1 r1) (Phoas.And l2 r2)
    | RelOr {l1 r1 : Phoas.prop A1} {l2 r2 : Phoas.prop A2} :
        RelProp w l1 l2 -> RelProp w r1 r2 -> RelProp w (Phoas.Or l1 r1) (Phoas.Or l2 r2)
    | RelForall {f1 : A1 -> Phoas.prop A1} {f2 : A2 -> Phoas.prop A2} :
        (forall (a1 : A1) (a2 : A2) w', acc w w' -> rel_A w' a1 a2 -> RelProp w' (f1 a1) (f2 a2)) ->
        RelProp w (Phoas.Forall f1) (Phoas.Forall f2)
    | RelCmp {r : Relop} {a1 b1 : A1} {a2 b2 : A2} :
        rel_A w a1 a2 -> rel_A w b1 b2 -> RelProp w (Phoas.Cmp r a1 b1) (Phoas.Cmp r a2 b2).

End Props.



(* ================================================================== *)
(* Part 3: Object-language specific relations                          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* 3.1 Logic variables and stores                                      *)
(* ------------------------------------------------------------------ *)

(* the operations of logic variables preserve relatedness *)
Class RelLogicVariable {World V1 V2 : Set} (LV1 : PL.LogicVariable V1) (LV2 : PL.LogicVariable V2)
  (rel_V : Related World V1 V2) := {
  rel_lit : forall w n, rel_V w (LV1.(PL.lit) n) (LV2.(PL.lit) n);
  rel_add : forall w a1 a2 b1 b2, rel_V w a1 a2 -> rel_V w b1 b2 ->
            rel_V w (LV1.(PL.add) a1 b1) (LV2.(PL.add) a2 b2)
}.

(* every variable is bound in both stores or in neither, to related values *)
Definition RelStore {World V1 V2 : Set} (rel_V : Related World V1 V2) :
  Related World (stringmap V1) (stringmap V2) :=
  fun w store1 store2 => forall x, RelOption rel_V w (store1 !! x) (store2 !! x).



(* ------------------------------------------------------------------ *)
(* 3.2 Concrete worlds: stores of values                               *)
(* ------------------------------------------------------------------ *)

(* a value and an expression that evaluates to it in Γ *)
Inductive RelExp (Γ : stringmap PL.Value) : PL.Value -> PL.Exp -> Prop :=
  | RelLit n :
      RelExp Γ n (PL.Lit n)
  | RelVar x v :
      Γ !! x = Some v -> RelExp Γ v (PL.Var x)
  | RelAdd v1 v2 e1 e2 :
      RelExp Γ v1 e1 -> RelExp Γ v2 e2 -> RelExp Γ (Z.add v1 v2) (PL.Add e1 e2).

(* Relating values to readers [R PL.Exp]: in every larger store, the reader,
   run in the scope of that store, gives an expression related to the value.
   Quantifying over larger stores makes [RelReader] closed under weakening. *)
Definition RelReader : Related (stringmap PL.Value) PL.Value (Phoas.R PL.Exp) :=
  fun Γ v m => forall Γ', Γ ⊆ Γ' -> RelExp Γ' v (m (dom Γ')).

Lemma rel_lit_exp (Γ : stringmap PL.Value) (n : PL.Value) :
  RelExp Γ (PL.valueLogicVariable.(PL.lit) n) (PL.expLogicVariable.(PL.lit) n).
Proof.
  constructor.
Qed.

Lemma rel_add_exp (Γ : stringmap PL.Value) (a1 : PL.Value) (a2 : PL.Exp) (b1 : PL.Value) (b2 : PL.Exp) :
  RelExp Γ a1 a2 -> RelExp Γ b1 b2 ->
  RelExp Γ (PL.valueLogicVariable.(PL.add) a1 b1) (PL.expLogicVariable.(PL.add) a2 b2).
Proof.
  intros Ha Hb.
  constructor; assumption.
Qed.

#[export] Instance rel_lv_exp : RelLogicVariable PL.valueLogicVariable PL.expLogicVariable RelExp := {
  rel_lit := rel_lit_exp;
  rel_add := rel_add_exp
}.

Lemma rel_weaken_exp (Γ Γ' : stringmap PL.Value) (v : PL.Value) (e : PL.Exp) :
  Γ ⊆ Γ' -> RelExp Γ v e -> RelExp Γ' v e.
Proof.
  intros Hsub He.
  induction He.
  - constructor.
  - (* a lookup that succeeds in Γ also succeeds in the larger Γ' *)
    constructor. eapply lookup_weaken; eassumption.
  - constructor; assumption.
Qed.

#[export] Instance rel_weakening_exp : RelWeakening subseteq RelExp := {
  rel_weaken := rel_weaken_exp
}.

Lemma rel_lit_reader (Γ : stringmap PL.Value) (n : PL.Value) :
  RelReader Γ (PL.valueLogicVariable.(PL.lit) n) (Phoas.R_logicVariable.(PL.lit) n).
Proof.
  intros Γ' Hsub.
  constructor.
Qed.

Lemma rel_add_reader (Γ : stringmap PL.Value) (a1 : PL.Value) (a2 : Phoas.R PL.Exp) (b1 : PL.Value) (b2 : Phoas.R PL.Exp) :
  RelReader Γ a1 a2 -> RelReader Γ b1 b2 ->
  RelReader Γ (PL.valueLogicVariable.(PL.add) a1 b1) (Phoas.R_logicVariable.(PL.add) a2 b2).
Proof.
  intros Ha Hb Γ' Hsub.
  constructor; [apply Ha | apply Hb]; exact Hsub.
Qed.

#[export] Instance rel_lv_reader : RelLogicVariable PL.valueLogicVariable Phoas.R_logicVariable RelReader := {
  rel_lit := rel_lit_reader;
  rel_add := rel_add_reader
}.

(* [RelReader] is closed under weakening by construction *)
Lemma rel_weaken_reader (Γ Γ' : stringmap PL.Value) (v : PL.Value) (m : Phoas.R PL.Exp) :
  Γ ⊆ Γ' -> RelReader Γ v m -> RelReader Γ' v m.
Proof.
  intros Hsub Hm Γ'' Hsub'.
  apply Hm. etransitivity; eassumption.
Qed.

#[export] Instance rel_weakening_reader : RelWeakening subseteq RelReader := {
  rel_weaken := rel_weaken_reader
}.



(* ------------------------------------------------------------------ *)
(* 3.3 HOAS and FOAS propositions                                      *)
(* ------------------------------------------------------------------ *)

(* a HOAS and a FOAS proposition that say the same thing in store Γ *)
Inductive RelHoasFoas : Related (stringmap PL.Value) Hoas.prop Foas.prop :=
  | RhfT Γ : RelHoasFoas Γ Hoas.T Foas.T
  | RhfF Γ : RelHoasFoas Γ Hoas.F Foas.F
  | RhfImplies Γ l1 r1 l2 r2 :
      RelHoasFoas Γ l1 l2 -> RelHoasFoas Γ r1 r2 ->
      RelHoasFoas Γ (Hoas.Implies l1 r1) (Foas.Implies l2 r2)
  | RhfAnd Γ l1 r1 l2 r2 :
      RelHoasFoas Γ l1 l2 -> RelHoasFoas Γ r1 r2 ->
      RelHoasFoas Γ (Hoas.And l1 r1) (Foas.And l2 r2)
  | RhfOr Γ l1 r1 l2 r2 :
      RelHoasFoas Γ l1 l2 -> RelHoasFoas Γ r1 r2 ->
      RelHoasFoas Γ (Hoas.Or l1 r1) (Foas.Or l2 r2)
  | RhfForall Γ (f : PL.Value -> Hoas.prop) (x : string) (body : Foas.prop) :
      (forall v, RelHoasFoas (<[x := v]> Γ) (f v) body) ->
      RelHoasFoas Γ (Hoas.Forall f) (Foas.Forall x body)
  | RhfCmp Γ r (a1 : PL.Value) (a2 : PL.Exp) (b1 : PL.Value) (b2 : PL.Exp) :
      RelExp Γ a1 a2 -> RelExp Γ b1 b2 ->
      RelHoasFoas Γ (Hoas.Cmp r a1 b1) (Foas.Cmp r a2 b2).



(* ------------------------------------------------------------------ *)
(* 3.4 Translation from FOAS and the verification condition generator  *)
(* ------------------------------------------------------------------ *)

Section Vcg.
  Variable (World : Set) (acc : relation World) (Hpreorder : PreOrder acc).
  Variable (V1 V2 : Set) (rel_V : Related World V1 V2)
           (LV1 : PL.LogicVariable V1) (LV2 : PL.LogicVariable V2).
  Variable (HLV : RelLogicVariable LV1 LV2 rel_V) (Hweaken : RelWeakening acc rel_V).

  (* worlds only grow: [acc] is reflexive and transitive *)
  #[local] Hint Extern 1 (acc _ _) => reflexivity : core.
  #[local] Hint Extern 2 (acc _ _) => (etransitivity; eassumption) : core.

  Notation "□ A" := (RelBox acc A%rel) (at level 50, A at level 9) : rel_scope.

  (* stores *)

  Lemma rel_store_weaken (w w' : World) (store1 : stringmap V1) (store2 : stringmap V2) :
    acc w w' -> RelStore rel_V w store1 store2 -> RelStore rel_V w' store1 store2.
  Proof using Hweaken V1 V2 World acc rel_V.
    intros Hacc Hstore x.
    eapply rel_option_weaken; eauto.
  Qed.

  Lemma rel_store_singleton (w : World) (x : string) (v1 : V1) (v2 : V2) :
    rel_V w v1 v2 -> RelStore rel_V w {[x := v1]} {[x := v2]}.
  Proof.
    intros Hv y.
    destruct (decide (y = x)) as [-> | Hne].
    - rewrite !lookup_singleton_eq. constructor. exact Hv.
    - rewrite !lookup_singleton_ne by congruence. constructor.
  Qed.

  Lemma rel_store_insert (w : World) (x : string) (v1 : V1) (v2 : V2)
    (store1 : stringmap V1) (store2 : stringmap V2) :
    rel_V w v1 v2 -> RelStore rel_V w store1 store2 ->
    RelStore rel_V w (<[x := v1]> store1) (<[x := v2]> store2).
  Proof.
    intros Hv Hstore y.
    destruct (decide (y = x)) as [-> | Hne].
    - rewrite !lookup_insert_eq. constructor. exact Hv.
    - rewrite !lookup_insert_ne by congruence. apply Hstore.
  Qed.

  Lemma rel_store_delete (w : World) (x : string) (store1 : stringmap V1) (store2 : stringmap V2) :
    RelStore rel_V w store1 store2 -> RelStore rel_V w (delete x store1) (delete x store2).
  Proof.
    intros Hstore y.
    destruct (decide (y = x)) as [-> | Hne].
    - rewrite !lookup_delete_eq. constructor.
    - rewrite !lookup_delete_ne by congruence. apply Hstore.
  Qed.

  Lemma rel_store_union (w : World) (store1 store1' : stringmap V1) (store2 store2' : stringmap V2) :
    RelStore rel_V w store1 store2 -> RelStore rel_V w store1' store2' ->
    RelStore rel_V w (store1 ∪ store1') (store2 ∪ store2').
  Proof.
    intros Hstore Hstore' x.
    rewrite !lookup_union.
    destruct (Hstore x); destruct (Hstore' x); constructor; assumption.
  Qed.

  (* translation from FOAS *)

  Lemma rel_interp_to_va_default (e : PL.Exp) (w : World)
    (store1 : stringmap V1) (store2 : stringmap V2)
    (Hstore : RelStore rel_V w store1 store2) :
    rel_V w (PL.interp_to_va_default LV1 store1 e) (PL.interp_to_va_default LV2 store2 e).
  Proof using HLV LV1 LV2 V1 V2 World rel_V.
    induction e; simpl.
    - apply rel_lit.
    - (* if x is in the stores, its values are related; otherwise we default to lit 0 *)
      destruct (Hstore x); [apply rel_lit | assumption].
    - apply rel_add; assumption.
  Qed.

  Lemma rel_interp_to_va_crash (e : PL.Exp) (w : World)
    (store1 : stringmap V1) (store2 : stringmap V2)
    (Hstore : RelStore rel_V w store1 store2) :
    RelOption rel_V w (PL.interp_to_va_crash LV1 store1 e) (PL.interp_to_va_crash LV2 store2 e).
  Proof using HLV LV1 LV2 V1 V2 World rel_V.
    induction e; simpl.
    - constructor. apply rel_lit.
    - apply Hstore.
    - destruct IHe1; [constructor |].
      destruct IHe2; [constructor |].
      constructor. apply rel_add; assumption.
  Qed.

  Lemma rel_foas_to_phoas (p : Foas.prop) (w : World)
    (store1 : stringmap V1) (store2 : stringmap V2)
    (Hstore : RelStore rel_V w store1 store2) :
    RelProp acc rel_V w (Phoas.foas_to_phoas LV1 store1 p) (Phoas.foas_to_phoas LV2 store2 p).
  Proof using HLV Hweaken LV1 LV2 V1 V2 World acc rel_V.
    revert w store1 store2 Hstore.
    induction p; intros w store1 store2 Hstore; simpl.
    - constructor.
    - constructor.
    - constructor; apply rel_interp_to_va_default; exact Hstore.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.
      intros v1 v2 w1 Hacc1 Hv.
      apply IHp.
      apply rel_store_insert; [exact Hv |].
      eapply rel_store_weaken; eauto.
  Qed.

  (* the store monad *)

  Definition RelPost {A1 A2 : Set} (rel_A : Related World A1 A2) :
    Related World (A1 -> stringmap V1 -> Phoas.prop V1) (A2 -> stringmap V2 -> Phoas.prop V2) :=
    rel_A ↣ RelStore rel_V ↣ RelProp acc rel_V.

  Definition RelWstore {A1 A2 : Set} (rel_A : Related World A1 A2) :
    Related World (vcg.Wstore V1 A1) (vcg.Wstore V2 A2) :=
    (□ (RelPost rel_A)) ↣ RelStore rel_V ↣ RelProp acc rel_V.

  Definition RelLift {A1 A2 B1 B2 : Set} (rel_A : Related World A1 A2) (rel_B : Related World B1 B2) :
    Related World (A1 -> vcg.Wstore V1 B1) (A2 -> vcg.Wstore V2 B2) :=
    rel_A ↣ RelWstore rel_B.

  Lemma rel_ret {A1 A2 : Set} (rel_A : Related World A1 A2) (w : World)
    (a1 : A1) (a2 : A2) (Ha : rel_A w a1 a2) :
    RelWstore rel_A w (vcg.ret a1) (vcg.ret a2).
  Proof using Hpreorder V1 V2 World acc rel_V.
    intros post1 post2 Hpost store1 store2 Hstore.
    eapply Hpost; eauto.
  Qed.

  Lemma rel_bind {A1 A2 B1 B2 : Set} (rel_A : Related World A1 A2) (rel_B : Related World B1 B2) (w : World)
    (m1 : vcg.Wstore V1 A1) (m2 : vcg.Wstore V2 A2)
    (k1 : A1 -> vcg.Wstore V1 B1) (k2 : A2 -> vcg.Wstore V2 B2)
    (Hm : RelWstore rel_A w m1 m2) (Hk : (□ (RelLift rel_A rel_B)) w k1 k2) :
    RelWstore rel_B w (vcg.bind m1 k1) (vcg.bind m2 k2).
  Proof using Hpreorder V1 V2 World acc rel_V.
    unfold vcg.bind, RelWstore, RelLift, RelPost, RelFunc, RelBox in *.
    intros post1 post2 Hpost store1 store2 Hstore.
    (* first run m, ... *)
    apply Hm; [| exact Hstore].
    intros w1 Hacc1 a1 a2 Ha store1' store2' Hstore1.
    (* ... then run k on its result *)
    apply (Hk w1 Hacc1 a1 a2 Ha); [| exact Hstore1].
    intros w2 Hacc2 b1 b2 Hb store1'' store2'' Hstore2.
    apply Hpost; [etransitivity; eassumption | exact Hb | exact Hstore2].
  Qed.

  Lemma rel_lookupWstore (w : World) (x : string) :
    RelWstore rel_V w (vcg.lookupWstore x) (vcg.lookupWstore x).
  Proof using Hpreorder V1 V2 World acc rel_V.
    unfold vcg.lookupWstore.
    intros post1 post2 Hpost store1 store2 Hstore.
    destruct (Hstore x).
    - constructor.
    - apply Hpost; eauto.
  Qed.

  Lemma rel_lookupWstore_safe (w : World) (x : string) :
    RelWstore (RelOption rel_V) w (vcg.lookupWstore_safe x) (vcg.lookupWstore_safe x).
  Proof using Hpreorder V1 V2 World acc rel_V.
    unfold vcg.lookupWstore_safe.
    intros post1 post2 Hpost store1 store2 Hstore.
    apply Hpost; eauto.
  Qed.

  Lemma rel_insertWstore (w : World) (x : string) (v1 : V1) (v2 : V2) (Hv : rel_V w v1 v2) :
    RelWstore RelUnit w (vcg.insertWstore x v1) (vcg.insertWstore x v2).
  Proof using Hpreorder V1 V2 World acc rel_V.
    unfold vcg.insertWstore.
    intros post1 post2 Hpost store1 store2 Hstore.
    apply (Hpost w ltac:(reflexivity) tt tt I).
    apply rel_store_insert; assumption.
  Qed.

  Lemma rel_deleteWstore (w : World) (x : string) :
    RelWstore RelUnit w (vcg.deleteWstore x) (vcg.deleteWstore x).
  Proof using Hpreorder V1 V2 World acc rel_V.
    unfold vcg.deleteWstore.
    intros post1 post2 Hpost store1 store2 Hstore.
    apply (Hpost w ltac:(reflexivity) tt tt I).
    apply rel_store_delete; assumption.
  Qed.

  Lemma rel_restoreWstore (w : World) (x : string) (o1 : option V1) (o2 : option V2)
    (Ho : RelOption rel_V w o1 o2) :
    RelWstore RelUnit w (vcg.restoreWstore x o1) (vcg.restoreWstore x o2).
  Proof using Hpreorder V1 V2 World acc rel_V.
    destruct Ho; simpl.
    - apply rel_deleteWstore.
    - apply rel_insertWstore; assumption.
  Qed.

  (* the verification condition generator *)

  Lemma rel_exec_exp (e : PL.Exp) (w : World) :
    RelWstore rel_V w (vcg.exec_exp LV1 e) (vcg.exec_exp LV2 e).
  Proof using HLV Hpreorder Hweaken LV1 LV2 V1 V2 World acc rel_V.
    revert w.
    induction e; intros w post1 post2 Hpost store1 store2 Hstore.
    - (* Lit *)
      simpl. eapply Hpost; eauto.
      apply rel_lit.
    - (* Var *)
      simpl. eapply rel_lookupWstore; eauto.
    - (* Add *)
      simpl. eapply rel_bind; eauto.
      intros w1 Hacc1 a1 a2 Ha.
      eapply rel_bind with (rel_A := rel_V).
      + apply IHe2.
      + intros w2 Hacc2 b1 b2 Hb.
        eapply rel_ret.
        apply rel_add.
        * eapply rel_weaken; eauto.
        * exact Hb.
  Qed.

  Lemma rel_exec_stm (stm : PL.Stm) (w : World) :
    RelWstore rel_V w (vcg.exec_stm LV1 stm) (vcg.exec_stm LV2 stm).
  Proof using HLV Hpreorder Hweaken LV1 LV2 V1 V2 World acc rel_V.
    revert w.
    induction stm; intros w; simpl.
    - apply rel_exec_exp.
    - eapply rel_bind.
      + apply rel_exec_exp.
      + intros w1 Hacc1 v1 v2 Hv.
        eapply rel_bind.
        * apply rel_lookupWstore_safe.
        * intros w2 Hacc2 previous1 previous2 Hprevious.
          eapply rel_bind.
          -- apply rel_insertWstore. eapply rel_weaken; eauto.
          -- intros w3 Hacc3 _ _ _.
             eapply rel_bind.
             ++ apply IHstm.
             ++ intros w4 Hacc4 result1 result2 Hresult.
                eapply rel_bind.
                ** apply rel_restoreWstore.
                   eapply (rel_option_weaken Hweaken); [| exact Hprevious]. eauto.
                ** intros w5 Hacc5 _ _ _.
                   eapply rel_ret.
                   eapply rel_weaken; eauto.
  Qed.

  Lemma rel_wp (stm : PL.Stm) (w : World)
    (post1 : V1 -> stringmap V1 -> Phoas.prop V1) (post2 : V2 -> stringmap V2 -> Phoas.prop V2)
    (store1 : stringmap V1) (store2 : stringmap V2)
    (Hpost : (□ (RelPost rel_V)) w post1 post2) (Hstore : RelStore rel_V w store1 store2) :
    RelProp acc rel_V w (vcg.wp LV1 stm post1 store1) (vcg.wp LV2 stm post2 store2).
  Proof using HLV Hpreorder Hweaken LV1 LV2 V1 V2 World acc rel_V.
    unfold vcg.wp.
    eapply rel_exec_stm; eauto.
  Qed.

  Lemma rel_vc (c : Foas.Contract) (w : World) :
    RelProp acc rel_V w (vcg.vc LV1 c) (vcg.vc LV2 c).
  Proof using HLV Hpreorder Hweaken LV1 LV2 V1 V2 World acc rel_V.
    destruct c as [forallVar pre prog arg result post].
    destruct prog as [functionName param body].
    simpl.
    (* the logic variable of the contract *)
    constructor.
    intros v1 v2 w1 Hacc1 Hv.
    constructor.
    - (* precondition *)
      apply rel_foas_to_phoas.
      apply rel_store_singleton. exact Hv.
    - (* weakest precondition of the body *)
      apply rel_wp.
      + (* postcondition: the forall variable and the result are in scope *)
        intros w2 Hacc2 result1 result2 Hresult store1 store2 Hstore.
        unfold vcg.ignore_map.
        apply rel_foas_to_phoas.
        apply rel_store_union; apply rel_store_singleton.
        * eapply rel_weaken; eauto.
        * exact Hresult.
      + (* initial store *)
        apply rel_store_singleton. exact Hv.
  Qed.

End Vcg.



(* ------------------------------------------------------------------ *)
(* 3.5 Translation to HOAS and FOAS                                    *)
(* ------------------------------------------------------------------ *)

Lemma rel_phoas_to_hoas_foas (Γ : stringmap PL.Value)
  (p1 : Phoas.prop PL.Value) (p2 : Phoas.prop (Phoas.R PL.Exp))
  (Hp : RelProp subseteq RelReader Γ p1 p2) :
  RelHoasFoas Γ (Hoas.phoas_to_hoas p1) (Phoas.phoas_to_foas (dom Γ) p2).
Proof.
  induction Hp; cbn.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - (* Forall: FOAS binds a fresh name x, HOAS gets an arbitrary value v *)
    constructor.
    intro v.
    set (x := fresh_string_of_set "x" (dom w)).
    unfold "∘".
    assert (Hdom : dom w ∪ {[x]} = dom (<[x:=v]> w)).
    { rewrite dom_insert_L. set_solver. }
    rewrite Hdom.
    apply H0.
    + (* the extended store is an extension, because x is fresh *)
      apply insert_subseteq.
      apply not_elem_of_dom.
      apply fresh_string_of_set_fresh.
    + (* v is related to the reader that always returns Var x *)
      intros Γ' Hsub.
      constructor.
      eapply lookup_weaken; [apply lookup_insert_eq | exact Hsub].
  - (* Cmp: run the readers in the scope of the current store *)
    constructor; [apply H | apply H0]; reflexivity.
Qed.



(* ------------------------------------------------------------------ *)
(* 3.6 The generated verification conditions are related              *)
(* ------------------------------------------------------------------ *)

Theorem rel_vc_hoas_foas (c : Foas.Contract) : RelHoasFoas ∅ (vcg.vc_hoas c) (vcg.vc_foas c).
Proof.
  apply rel_phoas_to_hoas_foas.
  apply (rel_vc _ rel_lv_reader rel_weakening_reader).
Qed.
