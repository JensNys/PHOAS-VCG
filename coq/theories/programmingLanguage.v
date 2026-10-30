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

  


Module PL.
Definition Value := Z.
(*Definition eval_store := listmap.string_map value.*)
Inductive Exp : Set :=
  | Lit (n : Z)
  | Var (x : string)
  | Add (e1 e2 : Exp).
Inductive Stm : Set :=
  | Expr (e : Exp)
  | Let (var:string) (e : Exp) (body:Stm).
Inductive Prog : Set :=
  | Fun (functionName : string) (param : string) (body : Stm).
  
  Class ValueAlgebra (V: Set) :=
  {
  lit : PL.Value -> V;
  add : V -> V -> V
  }.
  
  
  Instance value_valueAlgebra : ValueAlgebra (PL.Value) :=
  {
  lit := id;
  add := Z.add
  
  }.
  
  Instance expression_valueAlgebra : ValueAlgebra PL.Exp :=
  {
  lit := PL.Lit;
  add := PL.Add
  
  }.
  
(* I use big step semantics because it is closer to the interpreter i already have. 
The disadvantage of big step semantics is that it doesn't give a semantics to non-terminating programs. 
Since a contract and it postcondition makes a statement about terminating programs (If a program terminates with result r, {P} program {r.Q} holds). angelic/demonic choice determines whether a contract holds for non-terminating programs by either making the weakest precondition true or false.
therefore in our case i don't think we have a need for a small-step semantics. *)

(* big step semantics for expressions*)
Inductive evalExp (store : stringmap Value) :  Exp -> Value ->Prop :=
  | EvalLit : forall n , evalExp store (Lit n) n  
  | EvalVar : forall x  v,  lookup x store = Some v -> evalExp store (Var x)  v
  | EvalAdd : forall a b v1 v2, evalExp store a v1 -> evalExp store b  v2 -> evalExp store (Add a b)  (Z.add v1 v2).
  
(*big step semantics for statements*)
Inductive evalStm (store : stringmap Value) :  Stm  -> (Value * stringmap Value)->Prop :=
  | EvalExpr : forall mv e, evalExp store e  mv -> evalStm store (Expr e)  (mv,store)
  | EvalLetSucces  : forall x e body store' result v, evalExp store e (v) -> evalStm (insert x v store)  body (result,store')-> evalStm store (Let x e body)  (result, delete x store') .
  
Inductive evalProg : Prog->Value-> Value->Prop :=
  | EvalFunc: forall (functionName : string) (param : string) (body : Stm) input result o,  evalStm ({[ param := input ]}) body (result,o) -> evalProg (Fun functionName param body) input result.

Inductive wfexp (Γ : stringset) : Exp -> Prop :=
| WfLit n :
  wfexp Γ (Lit n)
| WfVar x :
  x ∈ Γ ->
  wfexp Γ (Var x)
| WfAdd e1 e2 :
  wfexp Γ e1 ->
  wfexp Γ e2 ->
  wfexp Γ (Add e1 e2).



Inductive wfStm (Γ : stringset)  : Stm -> Prop :=
  | WfExpr (e : Exp) :  wfexp Γ e -> wfStm Γ (Expr e)
  | WfLet (var:string) (e : Exp) (body:Stm) : wfexp Γ e -> wfStm (union Γ (singleton var)) body-> wfStm Γ (Let var e body) .


Inductive wfProg : Prog -> Prop :=
  | WfFun name param body: wfStm  (singleton param) body -> wfProg (Fun name param  body ).
  


  (*als ik een store heb en x \in (dom store) -> exists y: some y = lookup x store*)
  Definition contains_implies_lookup (V : Set) (store : stringmap V)  : forall x, x ∈ (dom store) -> {y | lookup x store = Some y}.
  Proof.
intros x H.
  apply elem_of_dom in H.
  (* H : is_Some (store !! x) *)
  unfold is_Some in H.
  (* Now case split on the actual map lookup *)
  destruct (lookup x store) as [y|] eqn:Heq.
  - exists y. reflexivity.
  - exfalso. destruct H as [y Hy]. congruence.
  
  Defined.






  Fixpoint interp_to_va_default (V : Set) (VA: ValueAlgebra V) (store:stringmap V) (e : Exp)  : V :=
    match e with
      |Lit n => lit n
      
      |Var x => match (lookup x store) with
                                          | None => lit 0%Z
                                          | Some v => v
                                       end

      | Add l r=> add (interp_to_va_default VA store l) (interp_to_va_default VA store r)
    end.
    
    Fixpoint interp_to_va_crash (V : Set) (VA: ValueAlgebra V) (store:stringmap V) (e : Exp) : option V :=
    match e with
    | Lit n => Some (lit n)
    | Var x => lookup x store
    | Add l r =>
        match interp_to_va_crash VA store l with
        | None => None
        | Some lv =>
            match interp_to_va_crash VA store r with
            | None => None
            | Some rv => Some (add lv rv)
            end
        end
    end.

    
  
  
                                           
    
    
      

End PL.
  
  



Inductive Relop : Set :=
  | Equal
  | GreaterThan
  | SmallerThan
  | GreaterThanEqual
  | SmallerThanEqual.

Fixpoint semant_Relop (r:Relop) : PL.Value->PL.Value->Prop :=
    match r with
      |Equal => eq
      |SmallerThan => Z.lt
      |GreaterThan => Z.gt
      |GreaterThanEqual => Z.ge
      |SmallerThanEqual => Z.le
    
    end.

Definition WF (World : Set) (X : Set) := World-> X -> Prop.
 
Module Foas.

 Inductive prop : Set :=
  | T
  | F
  | Cmp (r:Relop) (a b : PL.Exp)
  | Implies (l : prop) (r : prop)
  | And (l : prop) (r : prop)
  | Or (l : prop) (r : prop)
  | Forall (x : string) (p :  prop).

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

  
    
  Fixpoint semant' (store : stringmap PL.Value) (foasprop : Foas.prop) : Prop :=
    match foasprop with
    | Foas.T => True
    | Foas.F => False
    | Foas.Implies p1 p2 => semant' store p1 -> semant' store p2
    | Foas.And p1 p2 => semant' store p1 /\ semant' store p2
    | Foas.Or p1 p2 => semant' store p1 \/ semant' store p2
    | Foas.Forall x body =>
        forall arg, semant' (insert x arg store) body
    | Foas.Cmp cmp e1 e2 =>
        match PL.interp_to_va_crash PL.value_valueAlgebra store e1,
              PL.interp_to_va_crash PL.value_valueAlgebra store e2 with
        | Some v1, Some v2 => semant_Relop cmp v1 v2
        | _, _ => False
        end
    end.

  Definition semant (foasprop : Foas.prop) : Prop :=
    semant' empty foasprop.
  
  
  Inductive Contract := 
     | MkContract (forallVar : string) (pre : prop) (prog : PL.Prog) (arg : string) (result: string) (post : prop).

  
Check Foas.wfprop. 
  Definition wfContract (c : Contract) : Prop :=
  match c with
  | MkContract forallVar pre prog arg result post =>
      (Foas.wfprop (singleton forallVar) pre )*
      (forallVar = arg) *
      (forallVar <> result) *
     ( Foas.wfprop (union (singleton forallVar) (singleton result)) post)
  end.


  (*
  
  running the program with the right precondition will yield a result with the right postcondition.
  The precondition can mention varName
  *)
  Definition contract_semant (contract : Contract) : Prop :=
  forall varName pre prog argName resultName (post : prop),
    contract = MkContract varName pre prog argName resultName post ->
    forall inp result,
      semant' (insert argName inp empty) pre -> 
      (argName = varName) -> (* it is the only introduced logic variable *)
      PL.evalProg prog inp result ->
      semant' (insert resultName result (insert argName inp empty)) post.

  
    
    
  
    


    

     Set Printing Implicit.
    
  
  
End Foas.



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
  
  Fixpoint semant  (p : Phoas.prop (PL.Value)) : Prop :=
    match p with
    | Phoas.T _ => True
    | Phoas.F _ => False
    | Phoas.Implies l r => forall _: (semant l), (semant r)
    | Phoas.And l r => and (semant l) (semant r)
    | Phoas.Or l r => or (semant l) (semant r)
    | Phoas.Forall f =>   forall x, (semant (f x))
    | Phoas.Cmp r a b => (semant_Relop r) (a ) (b )
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
    
     

    
    



    Fixpoint foas_to_phoas (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V) (foasprop : Foas.prop)  : prop V :=
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


Class WF_VA (World : Set) (V:Set) (VA: PL.ValueAlgebra V) 
(WA: WF World V)  := {
    wf_lit : forall Γ n, WA Γ (VA.(PL.lit) n);
    wf_add : forall Γ v1 v2, WA Γ v1 -> WA Γ v2 -> WA Γ (VA.(PL.add) v1 v2);
}.





Definition WfStore (World : Set) (V : Set)  (WA :WF World V) : WF World (stringmap V) :=
    fun (w : World) (store : stringmap V)
     =>
    forall s v, (store !! s = Some v) -> (WA w v ).
 
 






Lemma wf_interp_to_va_default (World : Set) (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V) (e : PL.Exp)
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


Lemma wf_foas_to_phoas (World : Set) (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V)  (foasprop : Foas.prop) 
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



Lemma wf_foas_to_phoas2 (World : Set) (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V)  (foasprop : Foas.prop) (wfFoas : Foas.wfprop (dom store) foasprop ) :
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
  
  Instance R_valueAlgebra : PL.ValueAlgebra (stringset -> PL.Exp) :=
    {
    lit i:= ret (PL.Lit i);
    add x y := bind x (fun v1 => 
              bind y (fun v2 =>
              ret (PL.Add v1 v2)))
    }.


  Fixpoint phoas_to_foas (Γ : stringset) (p : Phoas.prop (PL.Exp)) : Foas.prop :=
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
             (f (PL.Var x)))
    | Phoas.Cmp r a b => Foas.Cmp r (a ) (b)
    end.

  Definition wfr : WF stringset (R PL.Exp) :=
    fun (Γ : stringset) (m : R PL.Exp)  => PL.wfexp Γ (m Γ).

  Definition wfe  : WF stringset (PL.Exp) :=
    fun (Γ : stringset) (m : PL.Exp) =>
        PL.wfexp Γ m.

  

  




  
  Lemma wf_phoas_to_foas  (Γ : stringset) (p : Phoas.prop (PL.Exp)) 
  (wfp : @Phoas.wfprop stringset subseteq (PL.Exp) wfe Γ p) :
    Foas.wfprop Γ (phoas_to_foas Γ p).
  Proof. 
    induction wfp; cbn.
    - constructor.
    - constructor.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.
      apply H0.
      + set_solver.
      + constructor.
      set_solver.
    - constructor; auto.
  Qed.


  Check foas_to_phoas.
  Definition foas_contract_to_phoas_contract (V : Set) (VA : PL.ValueAlgebra V) (env : stringmap V) (foas_contract : Foas.Contract) : Contract V :=
     match foas_contract with
      | Foas.MkContract forallVar pre prog  arg result post => ForallC (fun v => HoareTriple (foas_to_phoas VA {[ forallVar := v ]} pre) prog v (fun r => foas_to_phoas VA ({[ forallVar := v ]} ∪ {[ result := r ]} ) post))
     end .


Theorem wf_foas_to_phoas_contract (World : Set) (V : Set) (acc : relation World)
    (VA: PL.ValueAlgebra V)
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
  intros.
  unfold wfr. constructor.
  Qed.

  

  Lemma wf_add_expR : forall Γ v1 v2, wfr Γ v1 -> wfr Γ v2 -> wfr Γ (PL.add v1 v2).
  intros Γ v1 v2 H1 H2.
  constructor.
  - eapply H1.
  - eapply H2.
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
 
  
  Instance WF_VA_R: WF_VA  R_valueAlgebra  wfr  := {
    wf_lit := wf_lit_expR;
    wf_add := wf_add_expR
  }.

  Instance WF_VA_exp: WF_VA  PL.expression_valueAlgebra  wfe  := {
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


     Definition simplePropInverse : phoas_to_foas ∅ (@foas_to_phoas ( PL.Exp) PL.expression_valueAlgebra (empty : stringmap (PL.Exp)) simpleProp ) = simpleProp.
     Proof.
     
     vm_compute. reflexivity.  
     Qed.
     Set Printing Implicit.

     

   
End Phoas.

Module Hoas.


Inductive prop : Set :=
  | T
  | F
  | Implies (l : prop) (r : prop)
  | And (l : prop ) (r : prop)
  | Or (l : prop ) (r : prop)
  | Forall (f : PL.Value ->  prop)
  | Cmp (r:Relop) (a : PL.Value) (b:PL.Value).

  Fixpoint phoas_to_hoas (phoasProp : Phoas.prop PL.Value ) : prop :=
    match phoasProp with
      | Phoas.T _ => T
      | Phoas.F _=> F
      | Phoas.Implies l r => Implies (phoas_to_hoas l) (phoas_to_hoas r)
      | Phoas.And l r => And (phoas_to_hoas l) (phoas_to_hoas r)
      | Phoas.Or l r => Or (phoas_to_hoas l) (phoas_to_hoas r)
      | Phoas.Forall f => Forall (phoas_to_hoas ∘ f)
      | Phoas.Cmp c l r => Cmp c l r 
      end.
  Fixpoint hoas_to_phoas (phoasProp : prop) : Phoas.prop PL.Value  :=
    match phoasProp with
      | Forall f => Phoas.Forall (hoas_to_phoas ∘ f)
      | Cmp c l r => Phoas.Cmp c l r 
      | T => Phoas.T _
      | F => Phoas.F _
      | Implies l r => Phoas.Implies (hoas_to_phoas l) (hoas_to_phoas r)
      | And l r => Phoas.And (hoas_to_phoas l) (hoas_to_phoas r)
      | Or l r => Phoas.Or (hoas_to_phoas l) (hoas_to_phoas r)
      
      end.
  
  Inductive Contract  := 
     | ForallC (f: PL.Value -> Contract)
     | HoareTriple (pre : prop) (program : PL.Prog) (arg:PL.Value) (post :PL.Value -> prop).




  Fixpoint phoas_to_hoas_contract (c : Phoas.Contract PL.Value ) : Contract :=
    match c with
      | Phoas.ForallC f => ForallC (fun v => phoas_to_hoas_contract (f v))
      | Phoas.HoareTriple pre prog arg post => HoareTriple (phoas_to_hoas pre) prog arg (fun v => phoas_to_hoas (post v))
      end.

  Fixpoint hoas_to_phoas_contract (c : Contract) : Phoas.Contract PL.Value  :=
    match c with
      | ForallC f => Phoas.ForallC (fun v => hoas_to_phoas_contract (f v))
      | HoareTriple pre prog arg post => Phoas.HoareTriple (hoas_to_phoas pre) prog arg (fun v => hoas_to_phoas (post v))
      end.


  Lemma inverse_formula (p: Phoas.prop PL.Value) : hoas_to_phoas (phoas_to_hoas p) = p.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl. f_equal. unfold "∘".  extensionality v. apply H.
  - simpl. reflexivity.
  Qed.
  Lemma inverse_formula2 (p: prop) : phoas_to_hoas (hoas_to_phoas p) = p.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl. f_equal. unfold "∘".  extensionality v. apply H.
  - simpl. reflexivity.
  Qed.



  Lemma inverse_contract (c: Phoas.Contract PL.Value): hoas_to_phoas_contract (phoas_to_hoas_contract c) = c.
  induction c.
  -  simpl. f_equal.  extensionality v. apply H.
  - simpl. f_equal. 
    + apply (inverse_formula ).
    + extensionality v. apply inverse_formula.
  Qed.
  
  
  
  Fixpoint semant  (p : prop ) : Prop :=
    match p with
    | T => True
    | F => False
    | Implies l r => forall _: (semant l), (semant r)
    | And l r => and (semant l) (semant r)
    | Or l r => or (semant l) (semant r)
    | Forall f =>   forall x, (semant (f x))
    | Cmp r a b => (semant_Relop r) (a ) (b )
    end.
  
  Definition contract_semant (contract:Hoas.Contract ) :Prop := forall  pre prog (post : PL.Value->PL.Value->prop), 
       contract= (ForallC (fun v => HoareTriple (pre v) prog v (post v) )) -> 
       forall inp result, semant (pre inp) ->
               PL.evalProg prog inp result ->
               semant (post inp result).



  Lemma preserves_semantics (p:Phoas.prop PL.Value): Hoas.semant (Hoas.phoas_to_hoas p) <-> Phoas.semant p.
  Proof.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; try(rewrite IHp1; rewrite IHp2); reflexivity.
  - simpl; try(rewrite IHp1; rewrite IHp2); reflexivity.
  - simpl; try(rewrite IHp1; rewrite IHp2); reflexivity.
  - simpl. split. + intros. eapply H. eapply H0.
                  + intros. eapply H. eapply H0. 
  - simpl. reflexivity.
  Qed.  



End Hoas.





Module vcg.
Definition Wstore (V A:Set) := (A -> stringmap V -> Phoas.prop V) -> stringmap V -> Phoas.prop V.



  Definition ret (V A:Set) (a:A) : Wstore V A := fun post store => post a store.
  Definition bind (V A B:Set) (c : Wstore V A) (k : A->Wstore V B) : Wstore V B :=
  fun post store1 => c (fun a store2 => (k a) post store2) store1.

  Check WF.


  Section WFs.
  Variable (World : Set).
  Variable (acc : relation World).
  Variable  (pre : PreOrder acc).
  Variable ( V A: Set) (wfA :WF World A) (wfV :WF World V).
  Variable (VA : PL.ValueAlgebra V).
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
 

  
  Definition lookupWstore (V : Set)  (varname : string) : Wstore V V :=
  fun post store => match (lookup varname store) with 
                        | None => Phoas.F V
                        | Some value => post value store
                    end.

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

  Definition lookupWstore_safe (V : Set)  (varname : string) : Wstore V (option V) :=
  fun post store => post (lookup varname store) store.


Lemma wflookupWstore_safe  (w:World) (s : string)  : Wf_Wstore wfV (Wfoption wfV) w (lookupWstore_safe s).
  unfold lookupWstore_safe.
  unfold Wf_Wstore.
  unfold WfFunc.
  
  intros post H store wfStore .
  eapply H;eauto.

  unfold Wfoption.
  
  destruct (store !! s) eqn:Heq ;eauto.
  Qed.

  Definition insertWstore (V : Set)  (varname : string) (v:V) : Wstore V unit  :=
  fun post store => post tt (insert varname v store).

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


  Definition deleteWstore (V : Set)  (varname : string) : Wstore V unit  :=
  fun post store => post tt (delete varname store).

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
  



  
  Definition restoreWstore (V : Set)  (varname : string) (oldvalue : option V) : Wstore V unit  :=
  match oldvalue with
  | None => deleteWstore varname
  | Some v => insertWstore varname v
  end.



  Lemma wfrestoreWstore  (w:World) (varname : string) (opt_v:option V) (wf_opt : (Wfoption wfV) w opt_v) : Wf_Wstore wfV wf_unit w (restoreWstore varname opt_v).
 Proof using V World acc pre wfV.
  destruct opt_v as [v|]; simpl in *. 
  - apply wfinsertWstore.  exact wf_opt.
  - apply wfdeleteWstore.
  Qed.
  
  

  Fixpoint exec_exp (V:Set) (VA : PL.ValueAlgebra V) (e : PL.Exp) : (Wstore V V):= 
  match e with
  | PL.Lit n => ret (VA.(PL.lit) n)
  | PL.Var x => lookupWstore x
  | PL.Add e1 e2 => bind (exec_exp VA e1)  (fun x =>
                    bind (exec_exp VA e2)  (fun y =>
                    ret (VA.(PL.add) x y)
  
  ))
  end.



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

  


  

  
  
  Fixpoint exec_stm (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) : (Wstore V V):= 
  match stm with
  | PL.Expr e => exec_exp VA e
  | PL.Let var e body => bind (exec_exp VA e)                    (fun  x =>
                         bind (lookupWstore_safe var)            (fun  previous =>
                         bind (insertWstore var x)               (fun _ =>
                         bind (exec_stm VA body)                 (fun result =>
                         bind (restoreWstore var previous)       (fun _ =>
                         ret result
                         
                         )))))
  end.
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



  
  Definition wp (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.

  Lemma wf_wp
  (wfVA : Phoas.WF_VA VA wfV) (stm : PL.Stm)
    (w:World) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V)
      (Wfpost : (□ (WfPost wfV wfV)) w post) (WfinitStore : Phoas.WfStore wfV w initStore)
      : WfProp wfV w (wp VA stm post initStore).
  Proof using pre weaken.
    unfold wp.
    eapply wf_exec_stm; eauto.
  Qed.

  
  Definition ignore_map (V:Set) (post : V->Phoas.prop V) : V->stringmap V->Phoas.prop V :=
  fun result _ => post result.
  
  Fixpoint vc (V:Set) (VA : PL.ValueAlgebra V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | Phoas.ForallC f => Phoas.Forall (fun v => vc VA (f v))
    | Phoas.HoareTriple pre prog arg post =>
      match prog with 
        | PL.Fun functionName param body => (Phoas.Implies (pre) (wp VA body (ignore_map post) ({[ param := arg ]})))
      end
  end.

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


  Definition vc_hoas (c : Foas.Contract) : Hoas.prop :=
  Hoas.phoas_to_hoas (vc (PL.value_valueAlgebra) ((Phoas.foas_contract_to_phoas_contract PL.value_valueAlgebra  ∅ c))).
  
  Definition vc_foas (c : Foas.Contract) : Foas.prop :=
  Phoas.phoas_to_foas ∅ (vc (PL.expression_valueAlgebra) (Phoas.foas_contract_to_phoas_contract PL.expression_valueAlgebra  ∅ c)).


  Definition vc_just_hoas (c : Phoas.Contract PL.Value) : Hoas.prop :=
  Hoas.phoas_to_hoas (vc (PL.value_valueAlgebra) c).
  
  Lemma vc_hoas_unfold: forall (c  : Foas.Contract ), vc_hoas c = vc_just_hoas (Phoas.foas_contract_to_phoas_contract PL.value_valueAlgebra  ∅ c).
  Proof.
  intros. 
  reflexivity.
  Qed. 
  


End WFs.
  End vcg.

Section well_formed_generation.






Theorem wf_vc_foas : forall (c : Foas.Contract), Foas.wfprop empty (vcg.vc_foas c).
  intros c.
  
  eapply Phoas.wf_phoas_to_foas. (*phoas to foas*)
  eapply (vcg.wf_vc set_subseteq_preorder Phoas.weakening_wfe Phoas.WF_VA_exp). (*vc_foas*)
  apply (Phoas.wf_foas_to_phoas_contract _ _ _ Phoas.WF_VA_exp Phoas.weakening_wfe). (*foas to phoas contract*)
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




  Section Hoas_Sound.


  




  (*wp is a precondition*)
  (* If the generated weakest precondition holds, running the program will yield a result for wich the postcondition holds.  *)
  (* It might be better to prove this for wp with arbitrary input and map and applying here for a better induction hypothesis  *)
  Lemma wpPreconditionHoas : forall  (post : PL.Value->Hoas.prop) (stm : PL.Stm)  (inp : PL.Value) (arg : string) result fname,       
  (Phoas.semant (vcg.wp PL.value_valueAlgebra stm (vcg.ignore_map (Hoas.hoas_to_phoas ∘  post)) {[arg := inp]})) 
  ->
  (PL.evalProg (PL.Fun fname arg stm ) inp result)-> Hoas.semant (post result ).
  Proof.
  Admitted. (*if pre is a precondition*)
  




  

   Lemma translation_irrelevance : forall c pre prog post,
    Hoas.phoas_to_hoas_contract c =  Hoas.ForallC  (λ v : PL.Value,
                                                    Hoas.HoareTriple (pre v) prog v (post v))
  -> 
       c = Phoas.ForallC (λ v : PL.Value,
       Phoas.HoareTriple (Hoas.hoas_to_phoas (pre v)) prog v (fun result => Hoas.hoas_to_phoas (post v result))).
       
    Proof.
    intros.
    pose proof (f_equal Hoas.hoas_to_phoas_contract H) as H'.
    pose proof (Hoas.inverse_contract c) as H''.
    rewrite H'' in H'.
    simpl in H'.
    apply H'.
  Qed.


  (* when the vc returns a hoas proposition, it's correct wrt operational semantics of the Hoas contract *)
  Definition adequate (c : Phoas.Contract PL.Value) :
   Hoas.semant (vcg.vc_just_hoas c) ->  Hoas.contract_semant (Hoas.phoas_to_hoas_contract c).
  Proof.
  
  unfold Hoas.contract_semant.
  intros.
  (*intros.*)
  unfold vcg.vc_just_hoas in H.
  
  simpl in H.
  apply translation_irrelevance in H0.
  rewrite H0 in H.
  destruct prog.
  simpl in H.
  pose proof (Hoas.inverse_formula2 (pre inp)).
  specialize (H inp).
  rewrite H3 in H.
  
  
  Check (λ result : PL.Value,
                  Hoas.hoas_to_phoas
                    (post inp result)).
  Check wpPreconditionHoas.

  pose proof (@wpPreconditionHoas (post inp) body inp param result functionName) as Hwp.
  intros.
  apply (Hwp).
  - intros. apply H in H1.
    unfold "∘".
    pose proof (Hoas.preserves_semantics (vcg.wp PL.value_valueAlgebra body
              (vcg.ignore_map
                (λ result : PL.Value,
                    Hoas.hoas_to_phoas (post inp result)))
              {[param := inp]})).

    
    rewrite H4 in H1.
    exact H1.        
    - intros. exact H2.

  Qed.
  
  End Hoas_Sound.
  


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

  

 

Class Rel_VA (World : Set) (V1 V2:Set) (VA1 : PL.ValueAlgebra V1) ( VA2: PL.ValueAlgebra V2)
(Rel_V: Related World V1 V2)  := {
    rel_lit : forall Γ n, Rel_V Γ (VA1.(PL.lit) n) (VA2.(PL.lit) n);
    rel_add : forall Γ v1 v2 v1' v2', Rel_V Γ v1 v2-> Rel_V Γ v1' v2' -> Rel_V Γ (VA1.(PL.add) v1 v1') (VA2.(PL.add) v2 v2');
}.
Definition rel_lit_int_exp : forall Γ n, int_exp Γ (PL.value_valueAlgebra.(PL.lit) n) (PL.expression_valueAlgebra.(PL.lit) n).
Proof.
intros.
constructor.
Qed. 
Definition rel_add_int_exp : forall Γ v1 v2 v1' v2', int_exp Γ v1 v2-> int_exp Γ v1' v2' -> int_exp Γ (PL.value_valueAlgebra.(PL.add) v1 v1') (PL.expression_valueAlgebra.(PL.add) v2 v2').
Proof.
intros. 
constructor; [apply H |apply H0].
Qed.



Instance rel_va_int_exp : Rel_VA  (PL.value_valueAlgebra) (PL.expression_valueAlgebra) int_exp:=
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
  Variable (VAV1 : PL.ValueAlgebra V1) (VAV2 : PL.ValueAlgebra V2).
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

Lemma rel_phoas_to_hoas_foas  (Γ : stringmap PL.Value) (p1 : Phoas.prop (PL.Value)) (p2 : Phoas.prop (PL.Exp)) 
  (rel_p : @rel_prop (stringmap PL.Value) subseteq (PL.Value) (PL.Exp) int_exp Γ p1 p2) :
    rel_hoas_foas Γ (Hoas.phoas_to_hoas p1) (Phoas.phoas_to_foas (dom Γ) p2).
  Proof. 
    induction rel_p; cbn.
    - constructor.
    - constructor.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.  
    intro v.
    pose proof rel_weaken_int_exp.
    destruct H1 as [Hweaken'].
    set (x := fresh_string_of_set "x" (dom w)).
    unfold "∘".
    assert (dom w ∪ {[x]} = dom (<[x:=v]> w)).
    -- rewrite dom_insert_L.
       set_solver.
    --
    rewrite H1.
    eapply (H0).
      + Search "⊆".
      apply insert_subseteq.
      apply not_elem_of_dom.  
      apply fresh_string_of_set_fresh.
      
      + constructor.
        rewrite lookup_insert, decide_True by reflexivity. reflexivity.    
    - constructor; auto.
  Qed.



  Theorem rel_vc_hoas_foas : forall (c : Foas.Contract) , Foas.wfContract c -> rel_hoas_foas ∅ (vcg.vc_hoas c) (vcg.vc_foas c).
  intros c wfc.
  
  apply rel_phoas_to_hoas_foas. (*phoas to foas*)
  apply (rel_vc _ rel_weaken_int_exp rel_va_int_exp). (*vc_foas*)
  apply (rel_foas_to_phoas_contract _ _ _ ∅ ∅ c rel_va_int_exp wfc). (*foas to phoas contract*)
  Qed.


  Lemma int_exp_interp_to_va_crash {Γ : stringmap PL.Value} {v : PL.Value} {e : PL.Exp} :
  int_exp Γ v e -> PL.interp_to_va_crash PL.value_valueAlgebra Γ e = Some v.
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
  rel_value_exp store (PL.interp_to_va_default PL.value_valueAlgebra store e) e.
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
  rel_hoas_foas store (Hoas.phoas_to_hoas (Phoas.foas_to_phoas PL.value_valueAlgebra store p)) p . 
 
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
          rel_contract (Hoas.phoas_to_hoas_contract (Phoas.foas_contract_to_phoas_contract PL.value_valueAlgebra empty c)) c.
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
 Hoas.contract_semant (Hoas.phoas_to_hoas_contract (Phoas.foas_contract_to_phoas_contract PL.value_valueAlgebra empty c)) -> Foas.contract_semant c .
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
PL.value_valueAlgebra ∅ c))  *)

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