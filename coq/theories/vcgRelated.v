From Stdlib Require Import
  Classes.Morphisms
  NArith.BinNat
  Relations.Relation_Definitions
  ZArith.BinInt.

Require Import Coq.Strings.HexString.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Numbers.DecimalZ.
Require Import stdpp.gmap.
Require Import Coq.Program.Equality.

From stdpp Require Import options.
From Coq Require Import Program.Basics.
Local Open Scope program_scope.
From stdpp Require Import
  gmap mapset option stringmap.

Import EqNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.

From Phoas Require Import programmingLanguage foas phoas hoas vcGen hoasSoundness.

(* Executions of the vcg on related logic variables are related, and the closing soundness statements *)

Section Related.

Definition Related (World : Set) (T1 T2: Set) := World->T1->T2->Prop.

Inductive rel_value_exp (Γ : stringmap PL.Value) : PL.Value -> PL.Exp -> Prop :=
| Rel_Lit n :
  rel_value_exp Γ n (PL.Lit n)
| WfVar x v:
  Γ !! x = Some v ->
  rel_value_exp Γ v (PL.Var x)
| WfAdd e1 e2 v1 v2:
  rel_value_exp Γ v1 e1 ->
  rel_value_exp Γ v2 e2 ->
  rel_value_exp Γ (Z.add v1 v2) (PL.Add e1 e2).

Definition int_exp : Related (stringmap PL.Value) PL.Value PL.Exp :=
  fun world num exp => rel_value_exp world num exp.

  

 

Class Rel_VA (World : Set) (V1 V2:Set) (VA1 : PL.LogicVariable V1) ( VA2: PL.LogicVariable V2)
(Rel_V: Related World V1 V2)  := {
    rel_lit : forall Γ n, Rel_V Γ (VA1.(PL.lit) n) (VA2.(PL.lit) n);
    rel_add : forall Γ v1 v2 v1' v2', Rel_V Γ v1 v2-> Rel_V Γ v1' v2' -> Rel_V Γ (VA1.(PL.add) v1 v1') (VA2.(PL.add) v2 v2');
}.
Definition rel_lit_int_exp : forall Γ n, int_exp Γ (PL.valueLogicVariable.(PL.lit) n) (PL.expLogicVariable.(PL.lit) n).
Proof.
intros.
constructor.
Qed. 
Definition rel_add_int_exp : forall Γ v1 v2 v1' v2', int_exp Γ v1 v2-> int_exp Γ v1' v2' -> int_exp Γ (PL.valueLogicVariable.(PL.add) v1 v1') (PL.expLogicVariable.(PL.add) v2 v2').
Proof.
intros. 
constructor; [apply H |apply H0].
Qed.



Instance rel_va_int_exp : Rel_VA  (PL.valueLogicVariable) (PL.expLogicVariable) int_exp:=
  {
  rel_lit := rel_lit_int_exp;
  rel_add := rel_add_int_exp
  
  }.

  Inductive rel_opt (World : Set)  (T1 T2: Set) (rel_T :Related World T1 T2) (w:World) : option T1 -> option T2 -> Prop :=
    | rel_none : rel_opt rel_T w None None
    | rel_some (v1 : T1) (v2 : T2) : rel_T w v1 v2 -> rel_opt rel_T w (Some v1) (Some v2).

  Definition Rel_option (World : Set)  ( T1 T2: Set) (rel_T :Related World T1 T2) : Related World (option T1) (option T2) :=
    fun w mt1 mt2 =>  rel_opt rel_T w mt1 mt2.


Definition Rel_Store (World : Set) (V1 V2 : Set)  (rel_V :Related World V1 V2) : Related World (stringmap V1) (stringmap V2) :=
    fun (w : World) (store1 : stringmap V1) (store2 : stringmap V2)
     =>
    forall s, Rel_option rel_V w (store1 !! s) (store2 !! s) .
    




Class Related_Weakening (V1 V2:Set)  (World: Set) (Acc: relation World) (Rel_V: Related World V1 V2) := {
    weaken : forall (Γ Γ' : World) (v1:V1) (v2:V2), Acc Γ Γ' -> Rel_V Γ v1 v2 -> Rel_V Γ' v1 v2 
}.
Search stringmap.
Definition weaken_int_exp  : forall (Γ Γ' : stringmap PL.Value) (v1:PL.Value) (v2:PL.Exp), subseteq Γ Γ' -> int_exp Γ v1 v2 -> int_exp Γ' v1 v2 .
Proof.
intros Γ Γ' v1 v2 Hsub Hrel.
unfold int_exp in *.
induction Hrel .
- constructor.
- (* a lookup that succeeds in Γ also succeeds in the larger Γ' *)
  constructor. eapply lookup_weaken; eauto.
- constructor; eauto.
Qed.
Instance rel_weaken_int_exp : Related_Weakening subseteq int_exp:=
{
  weaken := weaken_int_exp

  }.

(* Relating values to readers [R PL.Exp]: in every larger store, the reader,
   run in the scope of that store, gives an expression related to the value.
   Quantifying over larger stores makes the relation closed under weakening. *)
Definition int_r : Related (stringmap PL.Value) PL.Value (Phoas.R PL.Exp) :=
  fun Γ v m => forall Γ', Γ ⊆ Γ' -> int_exp Γ' v (m (dom Γ')).

Definition rel_lit_int_r : forall Γ n, int_r Γ (PL.valueLogicVariable.(PL.lit) n) (Phoas.R_logicVariable.(PL.lit) n).
Proof.
intros Γ n Γ' Hsub.
constructor.
Qed.

Definition rel_add_int_r : forall Γ v1 v2 v1' v2', int_r Γ v1 v2 -> int_r Γ v1' v2' -> int_r Γ (PL.valueLogicVariable.(PL.add) v1 v1') (Phoas.R_logicVariable.(PL.add) v2 v2').
Proof.
intros Γ v1 v2 v1' v2' H1 H2 Γ' Hsub.
constructor; [apply H1 | apply H2]; exact Hsub.
Qed.

Instance rel_va_int_r : Rel_VA (PL.valueLogicVariable) (Phoas.R_logicVariable) int_r :=
  {
  rel_lit := rel_lit_int_r;
  rel_add := rel_add_int_r
  }.

Definition weaken_int_r : forall (Γ Γ' : stringmap PL.Value) (v1 : PL.Value) (v2 : Phoas.R PL.Exp), subseteq Γ Γ' -> int_r Γ v1 v2 -> int_r Γ' v1 v2.
Proof.
intros Γ Γ' v1 v2 Hsub Hrel Γ'' Hsub'.
apply Hrel. etransitivity; eassumption.
Qed.

Instance rel_weaken_int_r : Related_Weakening subseteq int_r :=
  {
  weaken := weaken_int_r
  }.

Section Related_props.

    Context {World : Set} (Acc : relation World) {pre : PreOrder Acc}.

    Variable (A1 A2 : Set).
    Variable (Rel_A :Related World A1 A2).
    Variable (Hweaken : Related_Weakening Acc Rel_A).
    Inductive rel_prop (w : World) : Phoas.prop A1 -> Phoas.prop A2 -> Prop :=
      | RelT : rel_prop w (Phoas.T A1) (Phoas.T A2)
      | RelF : rel_prop w (Phoas.F A1) (Phoas.F A2)
      | RelImplies {l1 r1 : Phoas.prop A1} {l2 r2 : Phoas.prop A2} :
                                   rel_prop w l1 l2 -> 
                                   rel_prop w r1 r2 -> 
                                   rel_prop w (Phoas.Implies l1 r1) (Phoas.Implies l2 r2)
      | RelAnd {l1 l2 r1 r2} :     rel_prop w l1 l2 -> 
                                   rel_prop w r1 r2 -> 
                                   rel_prop w (Phoas.And l1 r1) (Phoas.And l2 r2)
      | RelOr {l1 l2 r1 r2} :      rel_prop w l1 l2 ->
                                   rel_prop w r1 r2 -> 
                                   rel_prop w (Phoas.Or l1 r1) (Phoas.Or l2 r2)
      | RelForall {f1 : A1 -> Phoas.prop A1} {f2 : A2 -> Phoas.prop A2} :
          (forall a1 a2 w', Acc w w' -> Rel_A w' a1 a2 -> rel_prop w' (f1 a1) (f2 a2)) ->
          rel_prop w (Phoas.Forall f1) (Phoas.Forall f2)
      | RelCmp {r : Relop} {a1 b1 : A1} {a2 b2 : A2} : 
          Rel_A w a1 a2 -> Rel_A w b1 b2 -> 
          rel_prop w (Phoas.Cmp r a1 b1) (Phoas.Cmp r a2 b2).

  End Related_props.

  
  



  Section Rels.
  Variable (World : Set).
  Variable (acc : relation World).
  Variable  (preOrd : PreOrder acc).
  Variable ( V1 V2: Set) (rel_V :Related World V1 V2).
  Variable (VAV1 : PL.LogicVariable V1) (VAV2 : PL.LogicVariable V2).
  Variable (Hweaken : Related_Weakening acc rel_V).



Definition Rel_Func {World: Set} {A A' B B' : Set} (rel_A :Related World A A') (rel_B : Related World B B') : Related World (A -> B) (A' -> B') :=
fun w f f'=> forall (a:A) (a':A'), rel_A w a a'-> rel_B w (f a) (f' a').

Definition Box   {T1 T2: Set} (rel_T : Related World T1 T2)  : Related World T1 T2 :=
  fun w t1 t2 => forall w' , acc w w' -> rel_T w' t1 t2 .

Definition rel_unit : Related World unit unit :=
  fun w u1 u2 => True.

Declare Scope rel_scope.
Delimit Scope rel_scope with R.
 Open Scope rel_scope.
  Notation "A ↣ B" :=
      (Rel_Func A%R B%R)
        (at level 99, B at level 200, right associativity)
        : rel_scope.

  Notation "□ A"    := (Box A%R) (at level 50, A at level 9): rel_scope.

Lemma refl : forall w, acc w w.
  reflexivity.
  Qed.
  Hint Resolve refl : core.

  Lemma trans : forall w w' w'', acc w w' -> acc w' w'' -> acc w w''.

  etransitivity ;eauto.
  Qed.
  Hint Resolve trans : core.


  
 
    
  Definition Rel_prop  ( T1 T2: Set)  (rel_T :Related World T1 T2) : Related World (Phoas.prop T1) (Phoas.prop T2) :=
    fun w p1 p2 =>   (rel_prop acc rel_T) w p1 p2.





  Lemma Rel_option_weaken (w1 w2 : World) (o1 : option V1) (o2 : option V2) :
    acc w1 w2 -> Rel_option rel_V w1 o1 o2 -> Rel_option rel_V w2 o1 o2.
  Proof using Hweaken.
    intros.
    destruct H0.
    - constructor.
    - constructor. destruct  Hweaken. eapply Hweaken;eauto.
  Qed.

Inductive rel_Contract (w:World) :  Phoas.Contract V1 -> Phoas.Contract V2 -> Prop :=
  | Rel_ForallC {f1 : V1 -> Phoas.Contract V1} {f2 : V2 -> Phoas.Contract V2} :
        (forall (v1 : V1) (v2 : V2) w', acc w w' -> rel_V w' v1 v2 -> rel_Contract  w' (f1 v1) (f2 v2)) ->
        rel_Contract w (Phoas.ForallC f1) (Phoas.ForallC f2)
  | Rel_HoareTriple (pre1 : Phoas.prop V1) (pre2 : Phoas.prop V2) (program : PL.Prog) (arg1:V1) (arg2:V2) (post1 :V1 -> Phoas.prop V1) (post2 :V2 -> Phoas.prop V2):
        rel_prop acc rel_V w pre1 pre2 ->
        rel_V w arg1 arg2->
        (forall (result1 : V1) (result2 : V2) w', acc w w' -> rel_V w' result1 result2 ->
          rel_prop acc rel_V w' (post1 result1) (post2 result2)) -> 
          rel_Contract w (Phoas.HoareTriple pre1 program arg1 post1) (Phoas.HoareTriple pre2 program arg2 post2)
          .




  Definition Rel_Post ( V1 V2 A1 A2: Set) (rel_A :Related World A1 A2) (rel_V :Related World V1 V2): Related World (A1->stringmap V1 → Phoas.prop V1) (A2->stringmap V2 → Phoas.prop V2) :=
   rel_A  ↣ Rel_Store rel_V ↣ Rel_prop rel_V.


Definition Rel_Wstore ( V1 V2 A1 A2: Set) (rel_V :Related World V1 V2) (rel_A :Related World A1 A2)  :  Related World (vcg.Wstore V1 A1) (vcg.Wstore V2 A2):=
   (□ (Rel_Post rel_A rel_V)) ↣ (Rel_Store rel_V) ↣ (Rel_prop rel_V).



  Definition Rel_lift ( V1 V2 A1 A2 B1 B2: Set) (rel_V :Related World V1 V2) (rel_A :Related World A1 A2)  (rel_B :Related World B1 B2) : (Related World (A1 -> vcg.Wstore V1 B1) (A2 -> vcg.Wstore V2 B2)) :=
      rel_A ↣ (Rel_Wstore rel_V rel_B).


  


  Lemma rel_Ret  (C1 C2 : Set) (w:World) (c1 : C1) (c2 : C2) (rel_C : Related World C1 C2) (rel_c : rel_C w c1 c2) : Rel_Wstore rel_V rel_C w (vcg.ret c1) (vcg.ret c2).

  intros post1 post2 Hpost store Hstore.
  eapply Hpost;eauto.
  Qed.

  Lemma rel_Bind  (C1 C2 B1 B2: Set) (rel_C : Related World C1 C2)  (rel_B :Related World B1 B2) 
    (w:World) (c1 : vcg.Wstore V1 C1) (c2 : vcg.Wstore V2 C2) (k1 : C1->vcg.Wstore V1 B1) (k2 : C2->vcg.Wstore V2 B2) 
    (Rel_c : Rel_Wstore rel_V rel_C w c1 c2) (rel_k : Box ( Rel_lift rel_V rel_C rel_B ) w k1 k2) : Rel_Wstore rel_V rel_B w (vcg.bind c1 k1) (vcg.bind c2 k2).
    unfold vcg.bind.
    unfold Rel_Wstore.
    unfold Rel_Func.
    
    repeat unfold Rel_Wstore,Rel_Func,Rel_Post, Rel_prop, Box, Rel_lift in *.
    intros  post1 post2 H store1 store2 RelStore . 
    eauto.
    Qed.

  Lemma rel_lookupWstore  (w:World) (s : string)  : Rel_Wstore rel_V rel_V w (vcg.lookupWstore s) (vcg.lookupWstore s).
  unfold vcg.lookupWstore.
  unfold Rel_Wstore.
  intros post1 post2 H store1 store2 rel_Store .
  
  destruct (rel_Store s).
  - constructor. 
  - apply H;eauto. 
  Qed.

  
  Lemma rel_lookupWstore_safe  (w:World) (s : string)  : Rel_Wstore rel_V (Rel_option rel_V) w (vcg.lookupWstore_safe s) (vcg.lookupWstore_safe s).

  unfold vcg.lookupWstore_safe.
  unfold Rel_Wstore.
  unfold Rel_Func.
  
  intros post1 post2 H store1 store2 rel_Store .
  eapply H;eauto.

 Qed.

Lemma rel_insertWstore  (w:World) (varname : string) (v1:V1) (v2: V2) (rel_v : rel_V w v1 v2) :  (Rel_Wstore rel_V rel_unit w (vcg.insertWstore varname v1) (vcg.insertWstore varname v2)).
  unfold Rel_Wstore, Rel_Func, Rel_Post, Box, vcg.insertWstore ,"↣" ,Rel_prop.

  intros post1 post2 Hpost store1 store2 rel_Store.
  specialize (Hpost w (refl w) tt tt I).
  apply Hpost.
  intros s.
  specialize (rel_Store s).
  destruct (decide (s = varname)) as [-> | Hne1].
  - rewrite lookup_insert_eq . rewrite lookup_insert_eq . constructor.  exact rel_v.
  - rewrite lookup_insert_ne;eauto. rewrite lookup_insert_ne;eauto. 
  

  
  Qed.

 





  Lemma rel_deleteWstore  (w:World) (varname : string)  : Rel_Wstore rel_V rel_unit w (vcg.deleteWstore varname) (vcg.deleteWstore varname).
  unfold Rel_Wstore, Rel_Func, Rel_Post, Box, vcg.insertWstore ,"↣" ,Rel_prop.
  intros post1 post2 Hpost store1 store2 rel_Store.
  specialize (Hpost w (refl w) tt tt I ).
  apply Hpost.
  intros s .
  specialize (rel_Store s).
  destruct (decide (s = varname)) as [-> | Hne].
  - rewrite lookup_delete_eq . rewrite lookup_delete_eq . constructor.  
  -  rewrite lookup_delete_ne;eauto. rewrite lookup_delete_ne;eauto. 
  Qed.
  





Lemma rel_restoreWstore  (w:World) (varname : string) (opt_v1:option V1) (opt_v2:option V2) (rel_opt : (Rel_option rel_V) w opt_v1 opt_v2) : Rel_Wstore rel_V rel_unit w (vcg.restoreWstore varname opt_v1) (vcg.restoreWstore varname opt_v2).
 Proof using V1 V2 World acc preOrd rel_V.

 destruct rel_opt; simpl in *. 
  - apply rel_deleteWstore.
  - apply rel_insertWstore;eauto.
  
  Qed.

Lemma rel_exec_exp  
  (rel_VA : Rel_VA VAV1 VAV2 rel_V) (e : PL.Exp)  
    (w:World) 
      : Rel_Wstore rel_V rel_V w (vcg.exec_exp VAV1 e) (vcg.exec_exp VAV2 e).
  Proof using preOrd Hweaken.
  
   revert w.
   induction e;
   intros w post1 post2 Hpost store1 store2 rel_Store .

    (*Lit*)
   - simpl. eapply Hpost;eauto.  
    apply rel_lit.
    (*Var*)
   - simpl. eapply rel_lookupWstore; eauto.
   (*Add*)
   - simpl.  eapply rel_Bind;eauto. 
    intros w' Hacc x1 x2 Hx.
    eapply rel_Bind with (rel_C := rel_V).
    -- apply IHe2.
    --  intros w'' Hacc' x1' x2' Hx'.
        eapply rel_Ret.
        apply rel_add.
        ---  destruct Hweaken. eapply (weaken w' w'' x1 x2 Hacc' Hx).
        --- eauto.
   Qed.

Lemma rel_exec_stm  
  (rel_VA : Rel_VA VAV1 VAV2 rel_V) (stm : PL.Stm)  
    (w:World) 
      : Rel_Wstore rel_V rel_V w (vcg.exec_stm VAV1 stm) (vcg.exec_stm VAV2 stm).
revert w.
      induction stm; intros w;simpl.
      - apply rel_exec_exp;eauto.
      - eapply rel_Bind.
        -- apply rel_exec_exp;eauto.
        -- intros w' Hacc x1 x2 Hx.
        eapply rel_Bind.
        --- apply rel_lookupWstore_safe ;eauto.
        --- intros w'' Hacc' previous1 previous2 Hprevious.
        eapply rel_Bind.
        ---- apply rel_insertWstore ;eauto. destruct Hweaken. eapply weaken ; [apply Hacc'| apply Hx].
        ---- intros w''' Hacc'' _ _ _.
        eapply rel_Bind.
        ----- apply IHstm. 
        ----- intros w'''' Hacc''' result1 result2 Hresult.
        eapply rel_Bind.
        ------ apply rel_restoreWstore. eapply Rel_option_weaken ; [| exact Hprevious]. etransitivity; eauto.
        ------ intros w''''' Hacc'''' _ _ _.
        eapply rel_Ret.
        eapply weaken ; [apply Hacc''''| apply Hresult].
        Qed.

Lemma rel_wp
  (rel_VA : Rel_VA VAV1 VAV2 rel_V) (stm : PL.Stm)
    (w:World) (post1 : V1 -> stringmap V1 -> Phoas.prop V1) (post2 : V2 -> stringmap V2 -> Phoas.prop V2)  (initStore1 : stringmap V1) (initStore2 : stringmap V2)
      (Rel_post : (□ (Rel_Post rel_V rel_V)) w post1 post2) (Rel_initStore : Rel_Store rel_V w initStore1 initStore2)
      : Rel_prop rel_V w (vcg.wp VAV1 stm post1 initStore1) (vcg.wp VAV2 stm post2 initStore2).
  Proof using preOrd Hweaken.
    unfold vcg.wp.
    eapply rel_exec_stm; eauto.
  Qed.

  Lemma rel_vc
   (rel_VA : Rel_VA VAV1 VAV2 rel_V) (c1 : Phoas.Contract V1) (c2 : Phoas.Contract V2) (w : World): 
    rel_Contract w c1 c2 ->
    Rel_prop rel_V w (vcg.vc VAV1 c1) (vcg.vc VAV2 c2).
  Proof using preOrd Hweaken.
  intro rel_contract.
  induction rel_contract.
  - constructor.
  intros v1 v2 w' Hacc Hv.
  apply H0;eauto.
 
    (* HoareTriple *)
    - simpl.  
      destruct program as [functionName param body].
      constructor.
      + eauto.
      + apply rel_wp; auto.
        * 
          intros w' Hacc result1 result2 Hresult store1 store2 Hstore.
          unfold vcg.ignore_map.
          apply H1; eauto.
        * 
          intros s .
          destruct (decide (s = param)) as [-> | Hne].
          ** rewrite !lookup_singleton_eq. constructor. eauto.
          ** rewrite !lookup_singleton_ne;eauto. constructor.
Qed.


Lemma rel_interp_to_va_default (rel_VA : Rel_VA VAV1 VAV2 rel_V) (store1 : stringmap V1) (store2 : stringmap V2) (e : PL.Exp)
      (w : World) (rel_Store : Rel_Store rel_V w store1 store2 )  :
              rel_V w (PL.interp_to_va_default VAV1 store1 e) (PL.interp_to_va_default VAV2 store2 e).
Proof.
induction e; simpl.
- apply rel_lit.
- (* if x is in the store, the store is well-formed; otherwise we default to lit 0 *)
specialize (rel_Store x).

destruct rel_Store ;auto. 
apply rel_lit.
- apply rel_add; auto.
Qed.


Lemma rel_interp_to_va_crash (rel_VA : Rel_VA VAV1 VAV2 rel_V)
      (store1 : stringmap V1) (store2 : stringmap V2) (e : PL.Exp)
      (w : World) (rel_Store : Rel_Store rel_V w store1 store2) :
      Rel_option rel_V w (PL.interp_to_va_crash VAV1 store1 e) (PL.interp_to_va_crash VAV2 store2 e).
Proof.
induction e; simpl.
- constructor. apply rel_lit.
- (* if x is in the store, the store is well-formed; otherwise we default to lit 0 *)
destruct (rel_Store x);constructor;auto.

- destruct IHe1;try constructor.
  destruct IHe2;try constructor.
  apply rel_add;auto.

Qed.
  



Lemma rel_foas_to_phoas  (store1 : stringmap V1) (store2 : stringmap V2) (foasprop : Foas.prop) 
      (w : World) 
       (rel_Store : Rel_Store rel_V w store1 store2 ) (rel_VA : Rel_VA  VAV1 VAV2 rel_V) 
       : 
              @rel_prop World acc V1 V2 rel_V w (@Phoas.foas_to_phoas V1 VAV1 store1 foasprop) (@Phoas.foas_to_phoas V2 VAV2 store2 foasprop).
Proof using Hweaken V1 V2 VAV1 VAV2 World acc preOrd rel_V.
revert store1 store2 w rel_Store.
induction foasprop; intros store1 store2 w rel_Store; simpl.
- constructor.
- constructor.
- constructor; eapply rel_interp_to_va_default; eauto.
- constructor; auto.
- constructor; auto.
- constructor; auto.
- constructor. intros v1 v2 w' Hacc Hrelv.
  apply IHfoasprop.
  unfold Rel_Store.
  intros s .
  destruct (decide (s = x)) as [-> | Hne].
  + 
   rewrite lookup_insert_eq .
   rewrite lookup_insert_eq .
   constructor.
   eauto.
  +
   rewrite lookup_insert_ne  by congruence.
    rewrite lookup_insert_ne  by congruence.

    
     destruct (rel_Store s); try constructor; auto.
    
    destruct Hweaken .
    eapply (weaken0 w w' v0 v3 Hacc H); auto.
Qed.

Lemma rel_foas_to_phoas_contract 
    (w : World)
    (store1 : stringmap V1)
    (store2 : stringmap V2)
    (c : Foas.Contract) 
    (rel_VA :  Rel_VA VAV1 VAV2 rel_V)
    (wf_c : Foas.wfContract c)
    :
    
    rel_Contract w
      (Phoas.foas_contract_to_phoas_contract VAV1 store1 c) (Phoas.foas_contract_to_phoas_contract VAV2 store2 c).
Proof using Hweaken V1 V2 VAV1 VAV2 World acc preOrd rel_V.
destruct c as [forallVar pre prog arg result post].
  
  
  (* the translation wraps in ForallC *)
  simpl. apply Rel_ForallC.
  intros v1 v2 w' Hacc HrelV.
  (* now prove WfHoareTriple *)
  constructor.
  - 
    eapply rel_foas_to_phoas  ;eauto.
    
     intro s.
     destruct (decide (s = forallVar)) as [-> | Hne].
     -- rewrite !lookup_singleton_eq.
      constructor.
      auto.
     -- simpl.
      rewrite !lookup_singleton_ne;eauto.
      constructor.

  - auto.
  - 
    intros result_v1 result_v2 w'' Hacc' Hwfresult.
    eapply rel_foas_to_phoas  ;eauto.


    intros s.
    (* a lookup in the union comes from either the left or the right singleton *)
    
    rewrite !lookup_union.
    destruct (decide (s = forallVar)) as [-> | Hne].
    + rewrite !lookup_singleton_eq.
      rewrite !lookup_singleton_ne;eauto.
      ++ rewrite !(right_id_L None (∪)).  (* Some v1 ∪ None = Some v1 *)
         constructor.
         destruct Hweaken.
         apply (weaken0 w' w'' v1 v2 Hacc' HrelV).
      ++ destruct wf_c. destruct p. eauto.
      ++ destruct wf_c. destruct p. eauto.
    + destruct (decide (s = result)) as [-> | Hneres].
    ++ rewrite !lookup_singleton_eq.
      rewrite !lookup_singleton_ne;eauto.
      rewrite !(left_id_L None (∪)).  (* Some v1 ∪ None = Some v1 *)
         constructor.
         eauto.
    ++ rewrite !lookup_singleton_ne;eauto.
       rewrite !(left_id_L None (∪)).
       constructor.
Qed.


Inductive rel_hoas_foas : Related (stringmap PL.Value) Hoas.prop Foas.prop :=
| RHF_T Γ : rel_hoas_foas Γ Hoas.T Foas.T
| RHF_F Γ : rel_hoas_foas Γ Hoas.F Foas.F
| RHF_Implies Γ l1 r1 l2 r2 :
    rel_hoas_foas Γ l1 l2 -> rel_hoas_foas Γ r1 r2 ->
    rel_hoas_foas Γ (Hoas.Implies l1 r1) (Foas.Implies l2 r2)
| RHF_And Γ l1 r1 l2 r2 :
    rel_hoas_foas Γ l1 l2 -> rel_hoas_foas Γ r1 r2 ->
    rel_hoas_foas Γ (Hoas.And l1 r1) (Foas.And l2 r2)
| RHF_Or Γ l1 r1 l2 r2 :
    rel_hoas_foas Γ l1 l2 -> rel_hoas_foas Γ r1 r2 ->
    rel_hoas_foas Γ (Hoas.Or l1 r1) (Foas.Or l2 r2)
| RHF_Forall Γ (f : PL.Value -> Hoas.prop) (x : string) (body : Foas.prop) :
    (forall v, rel_hoas_foas (<[x := v]> Γ) (f v) body) ->
    rel_hoas_foas Γ (Hoas.Forall f) (Foas.Forall x body)
| RHF_Cmp Γ r (a b : PL.Value) (e1 e2 : PL.Exp) :
    int_exp Γ a e1 -> int_exp Γ b e2 ->
    rel_hoas_foas Γ (Hoas.Cmp r a b) (Foas.Cmp r e1 e2).



  
  

  




  End Rels.

Lemma rel_phoas_to_hoas_foas  (Γ : stringmap PL.Value) (p1 : Phoas.prop (PL.Value)) (p2 : Phoas.prop (Phoas.R PL.Exp)) 
  (rel_p : @rel_prop (stringmap PL.Value) subseteq (PL.Value) (Phoas.R PL.Exp) int_r Γ p1 p2) :
    rel_hoas_foas Γ (Hoas.phoas_to_hoas p1) (Phoas.phoas_to_foas (dom Γ) p2).
  Proof. 
    induction rel_p; cbn.
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



  Theorem rel_vc_hoas_foas : forall (c : Foas.Contract) , Foas.wfContract c -> rel_hoas_foas ∅ (vcg.vc_hoas c) (vcg.vc_foas c).
  intros c wfc.
  
  apply rel_phoas_to_hoas_foas. (*phoas to foas*)
  apply (rel_vc _ rel_weaken_int_r rel_va_int_r). (*vc_foas*)
  apply (rel_foas_to_phoas_contract _ _ _ ∅ ∅ c rel_va_int_r wfc). (*foas to phoas contract*)
  Qed.


  Lemma int_exp_interp_to_va_crash {Γ : stringmap PL.Value} {v : PL.Value} {e : PL.Exp} :
  int_exp Γ v e -> PL.interp_to_va_crash PL.valueLogicVariable Γ e = Some v.
  Proof.
    unfold int_exp.
    intro Hrel.

    induction Hrel;  simpl;eauto.
    - rewrite IHHrel1, IHHrel2. reflexivity.
  Qed.



  
  Lemma semant_hoas_foas_env (Γ : stringmap PL.Value) (hoas_prop : Hoas.prop) (foas_prop : Foas.prop) :
  rel_hoas_foas Γ hoas_prop foas_prop ->
  (Hoas.semant hoas_prop <-> Foas.semant' Γ foas_prop).
Proof.

intros Hrel.
induction Hrel;intros;simpl.

  - (* T *) reflexivity.
  - (* F *) reflexivity.
  - (* Implies *) rewrite IHHrel1, IHHrel2. reflexivity.
  - (* And *) rewrite IHHrel1, IHHrel2. reflexivity.
  - (* Or *) rewrite IHHrel1, IHHrel2. reflexivity.
  - split; intros Hall v; apply H0, Hall.
  - rewrite (int_exp_interp_to_va_crash H), (int_exp_interp_to_va_crash H0). reflexivity.
Qed.

(* if a hoas and foas proposition are related, then they are logically equivalent*)
Lemma semant_hoas_foas  (hoas_prop : Hoas.prop) (foas_prop : Foas.prop) :
  rel_hoas_foas empty hoas_prop foas_prop ->
  (Hoas.semant hoas_prop <-> Foas.semant foas_prop).
Proof.
unfold Foas.semant.
apply semant_hoas_foas_env.
Qed.

End Related.
  

Section Soundness.

(*I introduce a rel_contract relation so i can prove a correspondence between a foas contract and the hoas contract you get when translating the foas to a hoas contract.
  I will use then prove that related contracts have the same semantics
 *)
Inductive rel_contract : Hoas.Contract -> Foas.Contract -> Prop :=
| RelContract (forall_var arg result_name : string) (prog : PL.Prog)
    (pre_hoas : PL.Value -> Hoas.prop) (post_hoas : PL.Value -> PL.Value -> Hoas.prop)
    (pre_foas post_foas : Foas.prop) :
    (forall v, rel_hoas_foas (<[forall_var := v]> ∅) (pre_hoas v) pre_foas) ->
    (forall v res, rel_hoas_foas (<[result_name := res]> (<[forall_var := v]> ∅)) (post_hoas v res) post_foas) ->
    rel_contract (Hoas.ForallC (fun v => Hoas.HoareTriple (pre_hoas v) prog v (post_hoas v)))
                 (Foas.MkContract forall_var pre_foas prog arg result_name post_foas).

Lemma rel_contract_semant (h : Hoas.Contract) (c : Foas.Contract) :
  rel_contract h c -> Hoas.contract_semant h -> Foas.contract_semant c.
  Proof.
  intros Hrelated Hhoas_semant.
  induction Hrelated.

  intros varName pre' prog' argName resultName post' Heq inp result Hpre_f Harg Heval.
  specialize (H inp).
  specialize (H0 inp result).

injection Heq as Hforallvar_eq Hpre_eq Hprog_eq Harg_eq HresultName_eq Hpost_eq.
  subst varName pre' prog' argName resultName post' arg.
  pose proof (semant_hoas_foas_env H) as Hpre_equivalent.
  pose proof (semant_hoas_foas_env H0) as Hpost_equivalent.
  apply Hpost_equivalent.
  apply Hpre_equivalent in Hpre_f.
  unfold Hoas.contract_semant in Hhoas_semant.

  specialize (Hhoas_semant pre_hoas prog post_hoas eq_refl inp result).

  apply Hhoas_semant;eauto.
  Qed.


Lemma rel_interpret_exp (store : stringmap PL.Value) (e : PL.Exp) (wf_e : PL.wfexp (dom store) e) :
  rel_value_exp store (PL.interp_to_va_default PL.valueLogicVariable store e) e.
  Proof.
  induction wf_e.
  - simpl. constructor.
  - simpl.
    apply elem_of_dom in H. 
    destruct H.
    rewrite H.
    constructor;auto.
  - simpl. constructor;eauto.
  Qed.    

  
Lemma rel_foas_to_hoas (store : stringmap PL.Value) (p : Foas.prop) :
  Foas.wfprop (dom store) p ->
  rel_hoas_foas store (Hoas.phoas_to_hoas (Phoas.foas_to_phoas PL.valueLogicVariable store p)) p . 
 
  Proof.
  revert store.
  induction p; intros; simpl; constructor; try inversion H; eauto. (**;intros store wf_p ; simpl;constructor; eauto.*)

  - apply rel_interpret_exp;eauto. (*proof forall p, wfexp l -> (int_exp store interp l )l*) 
  - apply rel_interpret_exp;eauto.
  - intros; simpl. 
    apply IHp.
    rewrite dom_insert_L, union_comm_L.
    eauto.
  Qed.


  Lemma rel_contract_foas_to_hoas (c : Foas.Contract) (wf_c : Foas.wfContract c) : 
          rel_contract (Hoas.phoas_to_hoas_contract (Phoas.foas_contract_to_phoas_contract PL.valueLogicVariable empty c)) c.
  Proof.
  destruct c.
  simpl.

  destruct wf_c as [[[Hpre Harg] Hresult] Hpost]. 
  constructor;intros.
  - apply rel_foas_to_hoas. 
   rewrite dom_singleton_L.
   auto.
  -  (*apply rel_foas_to_hoas fails : Unable to unify "{[forallVar := v]} ∪ {[result := res]}" with "<[result:=res]> (<[forallVar:=v]> ∅)". *)
    assert (Heq : <[result:=res]> (<[forallVar:=v]> (∅ : stringmap PL.Value))
                  = {[forallVar := v]} ∪ {[result := res]}).
    -- rewrite insert_empty.
       Search insert.
       rewrite <- insert_union_singleton_r.
       --- reflexivity.
       --- apply lookup_singleton_ne. 
           exact Hresult.

    -- rewrite Heq.
       apply rel_foas_to_hoas.
       rewrite dom_union_L. 
       rewrite !dom_singleton_L.
       auto.
    Qed.
    
    
  
(* translating a Foas contract to a Hoas contract preserves its semantics *)
Lemma contract_translation_preserves_semantics (c : Foas.Contract) (wf_c : Foas.wfContract c):
 Hoas.contract_semant (Hoas.phoas_to_hoas_contract (Phoas.foas_contract_to_phoas_contract PL.valueLogicVariable empty c)) -> Foas.contract_semant c .
Proof.
intros Hoas_semant.

(*c is related to hoas c*)
pose proof (rel_contract_foas_to_hoas c wf_c) as Hrelated.
(*related c are equivalent*)
pose proof (rel_contract_semant Hrelated) as Hrelated_equiv.
apply Hrelated_equiv.
apply Hoas_semant.



Qed.

(* when the vc returns a hoas proposition, it's correct wrt operational semantics of the foas contract *)
Theorem hoas_adequate (c : Foas.Contract) (wf_c : Foas.wfContract c): 
      Hoas.semant (vcg.vc_hoas c) ->  Foas.contract_semant c.
Proof.
intros.
rewrite vcg.vc_hoas_unfold in *.
pose proof (adequate) as Hadequate.
pose proof (contract_translation_preserves_semantics) as Hpreserve.
apply (Hpreserve c);eauto.
(*specialize (Hadequate (Phoas.foas_contract_to_phoas_contract
PL.valueLogicVariable ∅ c))  *)

Qed.


(* 
If the verification condition is true, running the program with the right precondition will yield a result with the right postcondition.
*)
Theorem foas_adequate (c : Foas.Contract) (wf_c : Foas.wfContract c): 
      Foas.semant (vcg.vc_foas c) ->  Foas.contract_semant c.
Proof.
intros Foas_semant.
pose proof (rel_vc_hoas_foas c) as Hrelated.
pose proof (semant_hoas_foas (Hrelated wf_c)) as Hsemant_equivalent.
pose proof (@hoas_adequate c) as HoasSound.

apply Hsemant_equivalent in Foas_semant.   
specialize (HoasSound wf_c Foas_semant).
exact HoasSound.
Qed.

End Soundness.
