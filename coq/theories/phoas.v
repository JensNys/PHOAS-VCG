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

From Phoas Require Import programmingLanguage foas.

Definition WF (World : Set) (X : Set) := World-> X -> Prop.

Module Phoas.


Inductive prop (A : Set) : Set :=
  | T
  | F
  | Implies (l : prop A) (r : prop A)
  | And (l : prop A) (r : prop A)
  | Or (l : prop A) (r : prop A)
  | Forall (f : A ->  prop A)
  | Cmp (r:Relop) (a : A) (b:A).
  
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
  
  (* The semantics of a PHOAS proposition over any type of logic variables V:
     a quantifier ranges over values, which are injected into V with [lit],
     and comparisons use the [cmp] of the instance. *)
  Fixpoint semant {V : Set} {VA : PL.LogicVariable V} (p : Phoas.prop V) : Prop :=
    match p with
    | Phoas.T _ => True
    | Phoas.F _ => False
    | Phoas.Implies l r => forall _: (semant l), (semant r)
    | Phoas.And l r => and (semant l) (semant r)
    | Phoas.Or l r => or (semant l) (semant r)
    | Phoas.Forall f =>   forall v : PL.Value, (semant (f (PL.lit v)))
    | Phoas.Cmp r a b => PL.cmp r a b
    end.
  
  

  
  Inductive Contract (V:Set) := 
     | ForallC (f: V -> Contract V)
     | HoareTriple (pre : prop V) (program : PL.Prog) (arg:V) (post :V -> prop V).
  
  Inductive wfContract (World : Set) (V:Set) {acc : relation World} (wfV : WF World V) (w:World) :  Contract V -> Prop :=
  | WfForallC {f : V -> Contract V} :
        (forall (v : V) w', acc w w' -> wfV w' v -> wfContract  wfV w' (f v)) ->
        wfContract  wfV w (ForallC f)
  | WfHoareTriple (pre : prop V) (program : PL.Prog) (arg:V) (post :V -> prop V):
        wfprop acc wfV w pre ->
        wfV w arg ->
        (forall (result : V) w', acc w w' -> wfV w' result ->
          wfprop acc wfV w' (post result)) -> 
          wfContract wfV w (HoareTriple pre program arg post)
          .
    
     

    
    



    Fixpoint foas_to_phoas (V:Set) (VA: PL.LogicVariable V) (store : stringmap V) (foasprop : Foas.prop)  : prop V :=
    match foasprop with
    |Foas.T => T V
    |Foas.F => F V
    |Foas.Implies H1 H2 => Implies (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.And H1 H2=> And (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.Or H1 H2=> Or (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |@Foas.Forall x body  => 
        Forall (fun arg => @foas_to_phoas V VA (insert x arg store) body)
    |Foas.Cmp cmp l r => Cmp cmp (PL.interp_to_va_default VA store l) (PL.interp_to_va_default VA store r)
    end. 
     
     Check foas_to_phoas.


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



Lemma wf_foas_to_phoas2 (World : Set) (V:Set) (VA: PL.LogicVariable V) (store : stringmap V)  (foasprop : Foas.prop) (wfFoas : Foas.wfprop (dom store) foasprop ) :
      forall  (acc: relation World) (context : World) (WA : WF World V)
       (wfStore : WfStore ( WA) context store  ) (X : WF_VA VA WA ) 
       ( HaccElem: Weakening acc ( WA)), 
              @wfprop World acc V WA  context (@foas_to_phoas V VA store foasprop).
Proof.
  intros.
  apply wf_foas_to_phoas; auto.
Qed.

    
  Definition R (A : Set) : Set := stringset -> A.
  Definition ret (A:Set) (a:A) : R A := fun i => a.
  Definition bind (A B:Set) (m : R A) (k : A->R B) : R B :=
     fun r => k (m r) r.
  
  (* readers are compared by running them in the empty scope and comparing
     the resulting expressions *)
  #[global] Instance R_logicVariable : PL.LogicVariable (R PL.Exp) :=
    {
    lit i:= ret (PL.Lit i);
    add x y := bind x (fun v1 =>
              bind y (fun v2 =>
              ret (PL.Add v1 v2)));
    cmp r m1 m2 := PL.expLogicVariable.(PL.cmp) r (m1 ∅) (m2 ∅)
    }.


  (* The variables of the PHOAS proposition are readers [R PL.Exp]: expressions
     that are computed from the set of variable names in scope. *)
  Fixpoint phoas_to_foas (Γ : stringset) (p : Phoas.prop (R PL.Exp)) : Foas.prop :=
    match p with
    | Phoas.T _ => Foas.T
    | Phoas.F _ => Foas.F
    | Phoas.Implies l r => Foas.Implies (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.And l r => Foas.And (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.Or l r => Foas.Or (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.Forall f =>
        let x := fresh_string_of_set "x" Γ in
        Foas.Forall x
          (phoas_to_foas (union Γ (singleton x))
             (f (ret (PL.Var x))))
    | Phoas.Cmp r a b => Foas.Cmp r (a Γ) (b Γ)
    end.

  (* A reader is well-formed in Γ if it produces a well-formed expression in
     every larger scope. Quantifying over all larger scopes makes [wfr] closed
     under weakening (a reader may compute something different in a larger scope). *)
  Definition wfr : WF stringset (R PL.Exp) :=
    fun (Γ : stringset) (m : R PL.Exp)  => forall Γ', Γ ⊆ Γ' -> PL.wfexp Γ' (m Γ').

  Definition wfe  : WF stringset (PL.Exp) :=
    fun (Γ : stringset) (m : PL.Exp) =>
        PL.wfexp Γ m.

  

  




  
  Lemma wf_phoas_to_foas  (Γ : stringset) (p : Phoas.prop (R PL.Exp))
  (wfp : @Phoas.wfprop stringset subseteq (R PL.Exp) wfr Γ p) :
    Foas.wfprop Γ (phoas_to_foas Γ p).
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


  Check foas_to_phoas.
  Definition foas_contract_to_phoas_contract (V : Set) (VA : PL.LogicVariable V) (env : stringmap V) (foas_contract : Foas.Contract) : Contract V :=
     match foas_contract with
      | Foas.MkContract forallVar pre prog  arg result post => ForallC (fun v => HoareTriple (foas_to_phoas VA {[ forallVar := v ]} pre) prog v (fun r => foas_to_phoas VA ({[ forallVar := v ]} ∪ {[ result := r ]} ) post))
     end .


Theorem wf_foas_to_phoas_contract (World : Set) (V : Set) (acc : relation World)
    (VA: PL.LogicVariable V)
     (wfV : WF World V)
    (w : World)
    (env : stringmap V)
    (c : Foas.Contract) 
    (wfE' : WF_VA VA wfV)
    (weaken : Weakening acc wfV)
    :
    
    @wfContract World V acc wfV w
      (foas_contract_to_phoas_contract VA env c).
Proof.
  
  destruct c as [forallVar pre prog arg result post].
  
  
  (* the translation wraps in ForallC *)
  simpl. apply WfForallC.
  intros v w' Hacc Hwfv.
  (* now prove WfHoareTriple *)
  apply WfHoareTriple.
  - 
    eapply Phoas.wf_foas_to_phoas  ;eauto.
    
     
     intros s v' Hlookup.
      rewrite lookup_singleton_Some in Hlookup.
      destruct Hlookup as [_ ->].
      exact Hwfv.

  - 
    exact Hwfv.
  - 
    intros result_v w'' Hacc' Hwfresult.
    eapply Phoas.wf_foas_to_phoas  ;eauto.
    unfold WfStore.
    intros s v' Hlookup.
    (* a lookup in the union comes from either the left or the right singleton *)
    apply lookup_union_Some_raw in Hlookup.
    destruct Hlookup as [Hl | [_ Hl]];
      apply lookup_singleton_Some in Hl; destruct Hl as [_ <-].
    + (* the forall variable: well-formed in w', weaken to w'' *)
      exact (Phoas.weaken w' w'' v Hacc' Hwfv).
    + (* the result variable *)
      exact Hwfresult.
Qed.
  



  


     
  
   Definition simpleProp : Foas.prop  := Foas.Forall "x" 
                                                
                                                 (Foas.Cmp SmallerThan (PL.Lit 0%Z) (PL.Var "x")).
     

  
  
  Lemma wf_lit_expR: forall Γ n, wfr Γ (PL.lit n).
  Proof.
  intros Γ n Γ' Hsub.
  constructor.
  Qed.



  Lemma wf_add_expR : forall Γ v1 v2, wfr Γ v1 -> wfr Γ v2 -> wfr Γ (PL.add v1 v2).
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


     Definition simplePropInverse : phoas_to_foas ∅ (@foas_to_phoas (R PL.Exp) R_logicVariable (empty : stringmap (R PL.Exp)) simpleProp ) = simpleProp.
     Proof.
     
     vm_compute. reflexivity.  
     Qed.
     Set Printing Implicit.

     

   
End Phoas.
