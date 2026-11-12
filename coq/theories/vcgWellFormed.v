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

From Phoas Require Import programmingLanguage foas phoas hoas vcGen.

(* Well-formedness of the verification condition generator *)
Module vcg_wf.
Import vcg.

  Section WFs.
  Variable (World : Set).
  Variable (acc : relation World).
  Variable  (pre : PreOrder acc).
  Variable ( V A: Set) (wfA :WF World A) (wfV :WF World V).
  Variable (VA : PL.LogicVariable V).
  Variable (weaken : Phoas.Weakening acc wfV).

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
  reflexivity.
  Qed.
  Hint Resolve refl : core.

  Lemma trans : forall w w' w'', acc w w' -> acc w' w'' -> acc w w''.

  etransitivity ;eauto.
  Qed.
  Hint Resolve trans : core.



    
  Definition WfProp  (A: Set) (wfA : WF World A): WF World (Phoas.prop A) :=
    fun w p =>   (Phoas.wfprop acc wfA) w p.

  Definition Wfoption  (A: Set) (wfA : WF World A): WF World (option A) :=
    fun w ma =>  match (ma) with 
                        | None => True
                        | Some value => wfA w value
                    end.


  Lemma Wfoption_weaken (w1 w2 : World) (o : option V) :
    acc w1 w2 -> Wfoption wfV w1 o -> Wfoption wfV w2 o.
  Proof using weaken.
    destruct o as [v|]; unfold Wfoption; [apply Phoas.weaken | auto].
  Qed.



              
    
    


  Definition WfPost ( V A: Set) (wfA :WF World A) (wfV :WF World V): WF World (A->stringmap V → Phoas.prop V) :=
   wfA  ↣ Phoas.WfStore wfV ↣ WfProp wfV.


Definition Wf_Wstore (V A:Set)  (wfV :WF World V) (wfA : WF World A) : WF World (Wstore V A):=
   (□ (WfPost wfA wfV)) ↣ (Phoas.WfStore wfV) ↣ (WfProp wfV).



  Definition Wf_lift (V A B: Set) (wfV :WF World V) (wfA :WF World A) (wfB :WF World B) : (WF World (A -> Wstore V B)) :=
      wfA ↣ (Wf_Wstore wfV wfB).


  


  Lemma wfRet  (C : Set) (w:World) (c : C) (wfC : WF World C) (wf_c : wfC w c) : Wf_Wstore wfV wfC w (ret c).
  repeat unfold Wf_Wstore,WfFunc,WfPost, WfProp, Box.
  intros post Hpost store Hstore.
  eapply Hpost;eauto.
  Qed.



 

  
  

  Lemma wfBind  (C B: Set) (wfC : WF World C)  (wfB :WF World B) 
  (w:World) (c : Wstore V C) (k : C->Wstore V B) 
  (wf_c : Wf_Wstore wfV wfC w c) (wf_k : Box ( Wf_lift wfV wfC wfB ) w k) : Wf_Wstore wfV wfB w (bind c k).
  unfold bind.
  unfold Wf_Wstore.
  unfold WfFunc.
  
  repeat unfold Wf_Wstore,WfFunc,WfPost, WfProp, Box, Wf_lift in *.
  intros  post H store wfStore .

   eauto. 


 
   Qed.
 

   Lemma wflookupWstore  (w:World) (s : string)  : Wf_Wstore wfV wfV w (lookupWstore s).
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
  (wfVA : Phoas.WF_VA VA wfV) (e : PL.Exp)  
    (w:World) 
      : Wf_Wstore wfV wfV w (exec_exp VA e).
  Proof using pre weaken.
  
   revert w.
   induction e;
   intros w post Hpost store wfStore .

    (*Lit*)
   - simpl. eapply Hpost;eauto.  
    apply Phoas.wf_lit.
    (*Var*)
   - simpl. eapply wflookupWstore; eauto.
   (*Add*)
   - simpl.  eapply wfBind;eauto. 
    intros w' Hacc x Hx.
    eapply wfBind with (wfC := wfV).
    -- apply IHe2.
    --  intros w'' Hacc' x' Hx'.
        eapply wfRet.
        apply Phoas.wf_add.
        --- eapply (Phoas.weaken w' w'' x Hacc' Hx).
        --- eauto.
   Qed.
   
     
     
     
     






 Lemma WfStore_weaken  :
    forall w w' (s : stringmap V), 
    acc w w' -> Phoas.WfStore wfV w s -> Phoas.WfStore wfV w' s.
Proof using weaken.
  intros w w' s Hw Hs.
  unfold Phoas.WfStore.
  intros k v Hlookup.
  eapply Phoas.weaken.
  - exact Hw.
  - eapply Hs. exact Hlookup.
Qed.

  Lemma wf_exec_stm  
  (wfVA : Phoas.WF_VA VA wfV) (stm : PL.Stm)  
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
        ---- apply wfinsertWstore ;eauto. eapply Phoas.weaken ; [apply Hacc'| apply Hx].
        ---- intros w''' Hacc'' _ _.
        eapply wfBind.
        ----- apply IHstm. 
        ----- intros w'''' Hacc''' result Hresult.
        eapply wfBind.
        ------ apply wfrestoreWstore. eapply Wfoption_weaken ; [| exact Hprevious]. etransitivity; eauto.
        ------ intros w''''' Hacc'''' _ _.
        eapply wfRet.
        eapply Phoas.weaken ; [apply Hacc''''| apply Hresult].
        Qed.

  Lemma wf_wp
  (wfVA : Phoas.WF_VA VA wfV) (stm : PL.Stm)
    (w:World) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V)
      (Wfpost : (□ (WfPost wfV wfV)) w post) (WfinitStore : Phoas.WfStore wfV w initStore)
      : WfProp wfV w (wp VA stm post initStore).
  Proof using pre weaken.
    unfold wp.
    eapply wf_exec_stm; eauto.
  Qed.

  Lemma wf_vc
    (wfVA : Phoas.WF_VA VA wfV) (c : Phoas.Contract V) (w : World): 
    @Phoas.wfContract World V acc wfV  w c ->
    Phoas.wfprop acc wfV w (vc VA c).
    Proof using pre weaken.
    revert w.
    induction c as [f IH | pre' prog arg post]; intros w HwfContract; simpl.
    (* ForallC *)
    - inversion HwfContract as [? Hf |]; subst.
      constructor.
      intros v w' Hacc Hv.
      apply IH.
      apply Hf;eauto. 
    (* HoareTriple *)
    - inversion HwfContract as [| ? ? ? ? Hpre Harg Hpost]; subst.
      destruct prog as [functionName param body].
      constructor.
      + exact Hpre.
      + apply wf_wp; auto.
        * 
          intros w' Hacc result Hresult store Hstore.
          unfold ignore_map.
          apply Hpost; eauto.
        * 
          intros s v Hlookup.
          apply lookup_singleton_Some in Hlookup.
          destruct Hlookup as [_ <-].
          exact Harg.
    Qed.

End WFs.

End vcg_wf.

Section well_formed_generation.






Theorem wf_vc_foas : forall (c : Foas.Contract), Foas.wfprop empty (vcg.vc_foas c).
  intros c.
  
  eapply Phoas.wf_phoas_to_foas. (*phoas to foas*)
  eapply (vcg_wf.wf_vc set_subseteq_preorder Phoas.weakening_wfr Phoas.WF_VA_R). (*vc_foas*)
  apply (Phoas.wf_foas_to_phoas_contract _ _ _ Phoas.WF_VA_R Phoas.weakening_wfr). (*foas to phoas contract*)
Qed.





(*All phoas propositions are well-formed (meta-theoretical result that is not provable) *)
Lemma wf_all_phoas : forall (World V: Set) (wf_v : WF World V) (acc : relation World) (w : World) (p : Phoas.prop V),
                     Phoas.wfprop acc wf_v w p.
Admitted. 

(* same statemen of well-formedness. this time proven using the meta-theoretical result*)
Theorem wf_vc_foas' : forall (c : Foas.Contract), Foas.wfprop empty (vcg.vc_foas c).
  intros c.
  
  eapply Phoas.wf_phoas_to_foas. (*phoas to foas*)
  eapply wf_all_phoas.
Qed.









End well_formed_generation.
