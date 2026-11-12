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

(* Well-formedness (well-scopedness) of FOAS propositions and contracts *)
Module Foas_wf.
Import Foas.

  Inductive wfprop (Γ : stringset) : prop -> Prop :=
    | WfT : wfprop Γ T
    | WfF: wfprop Γ F
    | WfImplies l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Implies l r)
    | WfAnd l r : wfprop Γ l->wfprop Γ r->wfprop Γ (And l r)
    | WfOr l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Or l r)
    | WfCmp c l r :PL.wfexp Γ l -> PL.wfexp Γ r -> wfprop Γ (Cmp c l r)
    | WfForall (x : string) (body : prop) :
    wfprop (union Γ (singleton x)) body ->
    wfprop Γ (Foas.Forall x body).

Check Foas_wf.wfprop. 
  Definition wfContract (c : Contract) : Prop :=
  match c with
  | MkContract forallVar pre prog arg result post =>
      (Foas_wf.wfprop (singleton forallVar) pre )*
      (forallVar = arg) *
      (forallVar <> result) *
     ( Foas_wf.wfprop (union (singleton forallVar) (singleton result)) post)
  end.

End Foas_wf.


Definition WF (World : Set) (X : Set) := World-> X -> Prop.

(* Well-formedness of PHOAS propositions, contracts and their translations *)
Module Phoas_wf.
Import Phoas.

Class Weakening (V:Set)  (World: Set) (Acc: relation World) (WA: WF World V) := {
weaken : forall (Γ Γ' : World) (v:V), Acc Γ Γ' -> WA Γ v -> WA Γ' v
}.
  Section WithA.

    Context {World : Set} (Acc : relation World) {pre : PreOrder Acc}.

    Variable (A : Set).
    Variable (WA :WF World A).
    Variable (weaken : Weakening Acc WA).
    Inductive wfprop (w : World) : prop A -> Prop :=
    | WfT : wfprop w (T A)
    | WfF : wfprop w (F A)
    | WfImplies {l r} : wfprop w l -> wfprop w r -> wfprop w (Implies l r)
    | WfAnd {l r} : wfprop w l -> wfprop w r -> wfprop w (And l r)
    | WfOr {l r} : wfprop w l -> wfprop w r -> wfprop w (Or l r)
    | WfForall {f : A -> prop A} :
        (forall (a : A) w', Acc w w' -> WA w' a -> wfprop w' (f a)) ->
        wfprop w (Forall f)
    | WfCmp {r : Relop} {a b : A} : WA w a -> WA w b -> wfprop w (Cmp r a b).

  End WithA.


Class WF_VA (World : Set) (V:Set) (VA: PL.LogicVariable V) 
(WA: WF World V)  := {
    wf_lit : forall Γ n, WA Γ (VA.(PL.lit) n);
    wf_add : forall Γ v1 v2, WA Γ v1 -> WA Γ v2 -> WA Γ (VA.(PL.add) v1 v2);
}.





Definition WfStore (World : Set) (V : Set)  (WA :WF World V) : WF World (stringmap V) :=
    fun (w : World) (store : stringmap V)
     =>
    forall s v, (store !! s = Some v) -> (WA w v ).
 
 






Lemma wf_interp_to_va_default (World : Set) (V:Set) (VA: PL.LogicVariable V) (store : stringmap V) (e : PL.Exp)
      (context : World) WA
       (wfStore : WfStore WA context store ) (X : WF_VA VA WA) :
              WA context (PL.interp_to_va_default VA store e).
Proof.
induction e; simpl.
- apply wf_lit.
- (* if x is in the store, the store is well-formed; otherwise we default to lit 0 *)
  destruct (store !! x) as [v|] eqn:Hlookup.
  + eapply wfStore. exact Hlookup.
  + apply wf_lit.
- apply wf_add; auto.
Qed.


Lemma wf_foas_to_phoas (World : Set) (V:Set) (VA: PL.LogicVariable V) (store : stringmap V)  (foasprop : Foas.prop) 
      (acc: relation World) (context : World) (WA : WF World V)  
       (wfStore : WfStore WA context store ) (X : WF_VA VA WA) (Hweaken : Weakening  acc WA)
       : 
              @wfprop World acc V WA context (@foas_to_phoas V VA store foasprop).

Proof.
revert store context wfStore.
induction foasprop; intros store context wfStore; simpl.
- constructor.
- constructor.
- constructor; eapply wf_interp_to_va_default; eauto.
- constructor; auto.
- constructor; auto.
- constructor; auto.
- constructor. intros a w' Hacc Ha.
  apply IHfoasprop.
  intros s v Hlookup.
  destruct (decide (s = x)) as [-> | Hne].
  + rewrite lookup_insert_eq in Hlookup.
    injection Hlookup as <-.
    exact Ha.
  + rewrite lookup_insert_ne in Hlookup by congruence.
    apply (weaken context w'); auto.
    eapply wfStore. exact Hlookup.
Qed.



Lemma wf_foas_to_phoas2 (World : Set) (V:Set) (VA: PL.LogicVariable V) (store : stringmap V)  (foasprop : Foas.prop) (wfFoas : Foas_wf.wfprop (dom store) foasprop ) :
      forall  (acc: relation World) (context : World) (WA : WF World V)
       (wfStore : WfStore ( WA) context store  ) (X : WF_VA VA WA ) 
       ( HaccElem: Weakening acc ( WA)), 
              @wfprop World acc V WA  context (@foas_to_phoas V VA store foasprop).
Proof.
  intros.
  apply wf_foas_to_phoas; auto.
Qed.

  (* A reader is well-formed in Γ if it produces a well-formed expression in
     every larger scope. Quantifying over all larger scopes makes [wfr] closed
     under weakening (a reader may compute something different in a larger scope). *)
  Definition wfr : WF stringset (R PL.Exp) :=
    fun (Γ : stringset) (m : R PL.Exp)  => forall Γ', Γ ⊆ Γ' -> PL.wfexp Γ' (m Γ').

  Definition wfe  : WF stringset (PL.Exp) :=
    fun (Γ : stringset) (m : PL.Exp) =>
        PL.wfexp Γ m.

  

  




  
  Lemma wf_phoas_to_foas  (Γ : stringset) (p : Phoas.prop (R PL.Exp))
  (wfp : @Phoas_wf.wfprop stringset subseteq (R PL.Exp) wfr Γ p) :
    Foas_wf.wfprop Γ (phoas_to_foas Γ p).
  Proof.
    induction wfp; cbn.
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


  
  Lemma wf_lit_expR: forall Γ n, wfr Γ (PL.lit n).
  Proof.
  intros Γ n Γ' Hsub.
  constructor.
  Qed.



  Lemma wf_add_expR : forall Γ v1 v2, wfr Γ v1 -> wfr Γ v2 -> wfr Γ (PL.add v1 v2).
  Proof.
  intros Γ v1 v2 H1 H2 Γ' Hsub.
  constructor.
  - apply H1. exact Hsub.
  - apply H2. exact Hsub.
  Qed.

  Lemma wf_lit_exp: forall Γ n, wfe Γ (PL.Lit n).
  Proof.
  intros.
  unfold wfe. constructor.
  Qed.

  

  Lemma wf_add_exp : forall Γ v1 v2, wfe Γ v1 -> wfe Γ v2 -> wfe Γ (PL.Add v1 v2).
  Proof.
  intros Γ v1 v2 H1 H2.
  constructor.
  - eapply H1.
  - eapply H2.
  Qed. 
 
  
  Instance WF_VA_R: WF_VA  R_logicVariable  wfr  := {
    wf_lit := wf_lit_expR;
    wf_add := wf_add_expR
  }.

  Instance WF_VA_exp: WF_VA  PL.expLogicVariable  wfe  := {
    wf_lit := wf_lit_exp;
    wf_add := wf_add_exp
  }.
  
  

  Instance weakening_wfe : Weakening subseteq wfe.
  Proof.
  constructor.
  intros Γ Γ' v Hsub Hwf.
  unfold wfe in *.
  induction v.
  - constructor.
  - constructor. apply Hsub.  inversion Hwf. apply H0.
  - constructor; inversion Hwf;auto. 


  Qed.

  (* wfr is closed under weakening by construction *)
  Instance weakening_wfr : Weakening subseteq wfr.
  Proof.
  constructor.
  intros Γ Γ' m Hsub Hwf Γ'' Hsub'.
  apply Hwf. set_solver.
  Qed.


End Phoas_wf.


(* Well-formedness of the verification condition generator *)
Module vcg_wf.
Import vcg.

  Section WFs.
  Variable (World : Set).
  Variable (acc : relation World).
  Variable  (pre : PreOrder acc).
  Variable ( V A: Set) (wfA :WF World A) (wfV :WF World V).
  Variable (VA : PL.LogicVariable V).
  Variable (weaken : Phoas_wf.Weakening acc wfV).

Definition WfFunc {World: Set} {A B : Set} (wfA :WF World A) (wfB : WF World B) : WF World (A -> B) :=
fun w f => forall (a:A), wfA w a -> wfB w (f a).

  Definition Box {A : Set} (WA : WF World A)  : WF World A :=
    fun w a => forall w' , acc w w' -> WA w' a .


Declare Scope wf_scope.
Delimit Scope wf_scope with R.
 Open Scope wf_scope.
  Notation "A ↣ B" :=
      (WfFunc A%R B%R)
        (at level 99, B at level 200, right associativity)
        : wf_scope.

  Notation "□ A"    := (Box A%R) (at level 50, A at level 9): wf_scope.
 


        

Lemma refl : forall w, acc w w.
  Proof using World acc pre.
  reflexivity.
  Qed.
  Hint Resolve refl : core.

  Lemma trans : forall w w' w'', acc w w' -> acc w' w'' -> acc w w''.

  Proof using World acc pre.
  etransitivity ;eauto.
  Qed.
  Hint Resolve trans : core.



    
  Definition WfProp  (A: Set) (wfA : WF World A): WF World (Phoas.prop A) :=
    fun w p =>   (Phoas_wf.wfprop acc wfA) w p.

  Definition Wfoption  (A: Set) (wfA : WF World A): WF World (option A) :=
    fun w ma =>  match (ma) with 
                        | None => True
                        | Some value => wfA w value
                    end.


  Lemma Wfoption_weaken (w1 w2 : World) (o : option V) :
    acc w1 w2 -> Wfoption wfV w1 o -> Wfoption wfV w2 o.
  Proof using weaken.
    destruct o as [v|]; unfold Wfoption; [apply Phoas_wf.weaken | auto].
  Qed.



              
    
    


  Definition WfPost ( V A: Set) (wfA :WF World A) (wfV :WF World V): WF World (A->stringmap V → Phoas.prop V) :=
   wfA  ↣ Phoas_wf.WfStore wfV ↣ WfProp wfV.


Definition Wf_Wstore (V A:Set)  (wfV :WF World V) (wfA : WF World A) : WF World (Wstore V A):=
   (□ (WfPost wfA wfV)) ↣ (Phoas_wf.WfStore wfV) ↣ (WfProp wfV).



  Definition Wf_lift (V A B: Set) (wfV :WF World V) (wfA :WF World A) (wfB :WF World B) : (WF World (A -> Wstore V B)) :=
      wfA ↣ (Wf_Wstore wfV wfB).


  


  Lemma wfRet  (C : Set) (w:World) (c : C) (wfC : WF World C) (wf_c : wfC w c) : Wf_Wstore wfV wfC w (ret c).
  Proof using V World acc pre wfV.
  repeat unfold Wf_Wstore,WfFunc,WfPost, WfProp, Box.
  intros post Hpost store Hstore.
  eapply Hpost;eauto.
  Qed.



 

  
  

  Lemma wfBind  (C B: Set) (wfC : WF World C)  (wfB :WF World B) 
  (w:World) (c : Wstore V C) (k : C->Wstore V B) 
  (wf_c : Wf_Wstore wfV wfC w c) (wf_k : Box ( Wf_lift wfV wfC wfB ) w k) : Wf_Wstore wfV wfB w (bind c k).
  Proof using V World acc pre wfV.
  unfold bind.
  unfold Wf_Wstore.
  unfold WfFunc.
  
  repeat unfold Wf_Wstore,WfFunc,WfPost, WfProp, Box, Wf_lift in *.
  intros  post H store wfStore .

   eauto. 


 
   Qed.
 

   Lemma wflookupWstore  (w:World) (s : string)  : Wf_Wstore wfV wfV w (lookupWstore s).
  Proof using V World acc pre wfV.
  unfold lookupWstore.
  unfold Wf_Wstore.
  unfold WfFunc.
  repeat unfold Wf_Wstore,WfFunc,WfPost,  Box, Wf_lift in *.
  intros post H store wfStore .
  
  destruct (store !! s) eqn:Heq .
  - 
 
   eapply H;eauto. 
  - constructor.
  Qed.

Lemma wflookupWstore_safe  (w:World) (s : string)  : Wf_Wstore wfV (Wfoption wfV) w (lookupWstore_safe s).
  Proof using V World acc pre wfV.
  unfold lookupWstore_safe.
  unfold Wf_Wstore.
  unfold WfFunc.
  
  intros post H store wfStore .
  eapply H;eauto.

  unfold Wfoption.
  
  destruct (store !! s) eqn:Heq ;eauto.
  Qed.

  Definition wf_unit : WF World unit :=
  fun w u => True.

  Lemma wfinsertWstore  (w:World) (varname : string) (v:V) (wf_v : wfV w v) :  (Wf_Wstore wfV wf_unit w (insertWstore varname v)).
  Proof using V World acc pre wfV.
  unfold Wf_Wstore, WfFunc, WfPost, Box, insertWstore ,"↣" ,WfProp.
  intros post Hpost store wfStore.
  specialize (Hpost w (refl w) tt I).
  apply Hpost.
  intros s v' Hlookup.
  destruct (decide (s = varname)) as [-> | Hne].
  - rewrite lookup_insert_eq in Hlookup. injection Hlookup. intro veq. rewrite  <- veq. exact wf_v.
  -  rewrite lookup_insert_ne in Hlookup;eauto.
  Qed.

  Lemma wfdeleteWstore  (w:World) (varname : string)  : Wf_Wstore wfV wf_unit w (deleteWstore varname).
  Proof using V World acc pre wfV.
  unfold Wf_Wstore, WfFunc, WfPost, Box, insertWstore ,"↣" ,WfProp.
  intros post Hpost store wfStore.
  specialize (Hpost w (refl w) tt I).
  apply Hpost.
  intros s v' Hlookup.
  destruct (decide (s = varname)) as [-> | Hne].
  - rewrite lookup_delete_eq in Hlookup. discriminate. 
  -  rewrite lookup_delete_ne in Hlookup;eauto.
  Qed.

  Lemma wfrestoreWstore  (w:World) (varname : string) (opt_v:option V) (wf_opt : (Wfoption wfV) w opt_v) : Wf_Wstore wfV wf_unit w (restoreWstore varname opt_v).
 Proof using V World acc pre wfV.
  destruct opt_v as [v|]; simpl in *. 
  - apply wfinsertWstore.  exact wf_opt.
  - apply wfdeleteWstore.
  Qed.

  Lemma wf_exec_exp  
  (wfVA : Phoas_wf.WF_VA VA wfV) (e : PL.Exp)  
    (w:World) 
      : Wf_Wstore wfV wfV w (exec_exp VA e).
  Proof using pre weaken.
  
   revert w.
   induction e;
   intros w post Hpost store wfStore .

    (*Lit*)
   - simpl. eapply Hpost;eauto.  
    apply Phoas_wf.wf_lit.
    (*Var*)
   - simpl. eapply wflookupWstore; eauto.
   (*Add*)
   - simpl.  eapply wfBind;eauto. 
    intros w' Hacc x Hx.
    eapply wfBind with (wfC := wfV).
    -- apply IHe2.
    --  intros w'' Hacc' x' Hx'.
        eapply wfRet.
        apply Phoas_wf.wf_add.
        --- eapply (Phoas_wf.weaken w' w'' x Hacc' Hx).
        --- eauto.
   Qed.
   
     
     
     
     






 Lemma WfStore_weaken  :
    forall w w' (s : stringmap V), 
    acc w w' -> Phoas_wf.WfStore wfV w s -> Phoas_wf.WfStore wfV w' s.
Proof using weaken.
  intros w w' s Hw Hs.
  unfold Phoas_wf.WfStore.
  intros k v Hlookup.
  eapply Phoas_wf.weaken.
  - exact Hw.
  - eapply Hs. exact Hlookup.
Qed.

  Lemma wf_exec_stm  
  (wfVA : Phoas_wf.WF_VA VA wfV) (stm : PL.Stm)  
    (w:World) 
      : Wf_Wstore wfV wfV w (exec_stm VA stm).
      Proof using V VA World acc pre weaken wfV.
      revert w.
      induction stm; intros w;simpl.
      - apply wf_exec_exp;eauto.
      - eapply wfBind.
        -- apply wf_exec_exp;eauto.
        -- intros w' Hacc x Hx.
        eapply wfBind.
        --- apply wflookupWstore_safe ;eauto.
        --- intros w'' Hacc' previous Hprevious.
        eapply wfBind.
        ---- apply wfinsertWstore ;eauto. eapply Phoas_wf.weaken ; [apply Hacc'| apply Hx].
        ---- intros w''' Hacc'' _ _.
        eapply wfBind.
        ----- apply IHstm. 
        ----- intros w'''' Hacc''' result Hresult.
        eapply wfBind.
        ------ apply wfrestoreWstore. eapply Wfoption_weaken ; [| exact Hprevious]. etransitivity; eauto.
        ------ intros w''''' Hacc'''' _ _.
        eapply wfRet.
        eapply Phoas_wf.weaken ; [apply Hacc''''| apply Hresult].
        Qed.

  Lemma wf_wp
  (wfVA : Phoas_wf.WF_VA VA wfV) (stm : PL.Stm)
    (w:World) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V)
      (Wfpost : (□ (WfPost wfV wfV)) w post) (WfinitStore : Phoas_wf.WfStore wfV w initStore)
      : WfProp wfV w (wp VA stm post initStore).
  Proof using pre weaken.
    unfold wp.
    eapply wf_exec_stm; eauto.
  Qed.

  Lemma wf_vc
    (wfVA : Phoas_wf.WF_VA VA wfV) (c : Foas.Contract) (w : World):
    Phoas_wf.wfprop acc wfV w (vc VA c).
    Proof using pre weaken.
    destruct c as [forallVar pre' prog arg result post].
    destruct prog as [functionName param body].
    simpl.
    (* the logic variable of the contract *)
    constructor.
    intros v w' Hacc Hv.
    constructor.
    (* precondition *)
    - eapply Phoas_wf.wf_foas_to_phoas; eauto.
      intros s v' Hlookup.
      apply lookup_singleton_Some in Hlookup.
      destruct Hlookup as [_ <-].
      exact Hv.
    (* weakest precondition of the body *)
    - apply wf_wp; auto.
      + (* postcondition *)
        intros w'' Hacc' result_v Hresult store Hstore.
        unfold ignore_map.
        eapply Phoas_wf.wf_foas_to_phoas; eauto.
        intros s v' Hlookup.
        (* a lookup in the union comes from either the left or the right singleton *)
        apply lookup_union_Some_raw in Hlookup.
        destruct Hlookup as [Hl | [_ Hl]];
          apply lookup_singleton_Some in Hl; destruct Hl as [_ <-].
        * (* the forall variable: well-formed in w', weaken to w'' *)
          exact (Phoas_wf.weaken w' w'' v Hacc' Hv).
        * (* the result variable *)
          exact Hresult.
      + (* initial store *)
        intros s v' Hlookup.
        apply lookup_singleton_Some in Hlookup.
        destruct Hlookup as [_ <-].
        exact Hv.
    Qed.

End WFs.

End vcg_wf.

Section well_formed_generation.






Theorem wf_vc_foas : forall (c : Foas.Contract), Foas_wf.wfprop empty (vcg.vc_foas c).
  Proof.
  intros c.
  
  eapply Phoas_wf.wf_phoas_to_foas. (*phoas to foas*)
  apply (vcg_wf.wf_vc set_subseteq_preorder Phoas_wf.weakening_wfr Phoas_wf.WF_VA_R). (*vc_foas*)
Qed.





(*All phoas propositions are well-formed (meta-theoretical result that is not provable) *)
Lemma wf_all_phoas : forall (World V: Set) (wf_v : WF World V) (acc : relation World) (w : World) (p : Phoas.prop V),
                     Phoas_wf.wfprop acc wf_v w p.
Proof.
Admitted. 

(* same statemen of well-formedness. this time proven using the meta-theoretical result*)
Theorem wf_vc_foas' : forall (c : Foas.Contract), Foas_wf.wfprop empty (vcg.vc_foas c).
  Proof.
  intros c.
  
  eapply Phoas_wf.wf_phoas_to_foas. (*phoas to foas*)
  eapply wf_all_phoas.
Qed.









End well_formed_generation.
