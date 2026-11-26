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

From Phoas Require Import programmingLanguage foas.




(* introduces phoas propositions, their semantics and how to translate them from and to foas.*)
Module Phoas.

  



Inductive prop (A : Set) : Set :=
  | T
  | F
  | Implies (l : prop A) (r : prop A)
  | And (l : prop A) (r : prop A)
  | Or (l : prop A) (r : prop A)
  | Forall (f : A ->  prop A)
  | Exists (f : A ->  prop A)
  | Cmp (r:Relop) (a : A) (b:A).


  (* the operations of the language that the VC generator needs on logic variables *)
  Class LogicVariable (V: Set) :=
  {
  lit : PL.Value -> V;
  add : V -> V -> V
  }.

  (* comparison of logic variables; only needed to give a semantics to PHOAS propositions *)
  Class LogicComparison (V: Set) :=
  {
  cmp : Relop -> V -> V -> Prop
  }.

  #[global] Instance valueLogicVariable : LogicVariable (PL.Value) :=
  {
  lit := id;
  add := Z.add
  }.

  #[global] Instance valueLogicComparison : LogicComparison (PL.Value) :=
  {
  cmp := semant_Relop
  }.

  Fixpoint interp_to_va_default (V : Set) (VA: LogicVariable V) (store:stringmap V) (e : PL.Exp)  : V :=
    match e with
      |PL.Lit n => lit n
      
      |PL.Var x => match (lookup x store) with
                                          | None => lit 0%Z
                                          | Some v => v
                                       end

      | PL.Add l r=> add (interp_to_va_default VA store l) (interp_to_va_default VA store r)
    end.
    
    Fixpoint interp_to_va_crash (V : Set) (VA: LogicVariable V) (store:stringmap V) (e : PL.Exp) : option V :=
    match e with
    | PL.Lit n => Some (lit n)
    | PL.Var x => lookup x store
    | PL.Add l r =>
        match interp_to_va_crash VA store l with
        | None => None
        | Some lv =>
            match interp_to_va_crash VA store r with
            | None => None
            | Some rv => Some (add lv rv)
            end
        end
    end.

  #[global] Instance expLogicVariable : LogicVariable PL.Exp :=
  {
  lit := PL.Lit;
  add := PL.Add
  }.




  Definition phoas_example {V : Set} `{Phoas.LogicVariable V} : Phoas.prop V :=
  Forall (fun x => Cmp SmallerThanEqual x (add x (lit 1%Z))).
  
  (* The semantics of a PHOAS proposition over any type of logic variables V:
     a quantifier ranges over values, which are injected into V with [lit],
     and comparisons use [cmp] of the [LogicComparison] instance. *)
  Fixpoint semant {V : Set} {VA : Phoas.LogicVariable V} {VC : Phoas.LogicComparison V}
    (p : Phoas.prop V) : Prop :=
    match p with
    | Phoas.T _ => True
    | Phoas.F _ => False
    | Phoas.Implies l r => forall _: (semant l), (semant r)
    | Phoas.And l r => and (semant l) (semant r)
    | Phoas.Or l r => or (semant l) (semant r)
    | Phoas.Forall f =>   forall v : PL.Value, (semant (f (Phoas.lit v)))
    | Phoas.Exists f =>   exists v : PL.Value, (semant (f (Phoas.lit v)))
    | Phoas.Cmp r a b => Phoas.cmp r a b
    end.
  
  

  
    Fixpoint foas_to_phoas (V:Set) (VA: Phoas.LogicVariable V) (store : stringmap V) (foasprop : Foas.prop)  : prop V :=
    match foasprop with
    |Foas.T => T V
    |Foas.F => F V
    |Foas.Implies H1 H2 => Implies (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.And H1 H2=> And (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.Or H1 H2=> Or (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |@Foas.Forall x body  => 
        Forall (fun arg => @foas_to_phoas V VA (insert x arg store) body)
    |@Foas.Exists x body  =>
        Exists (fun arg => @foas_to_phoas V VA (insert x arg store) body)
    |Foas.Cmp cmp l r => Cmp cmp (Phoas.interp_to_va_default VA store l) (Phoas.interp_to_va_default VA store r)
    end. 
     
     Check foas_to_phoas.

    
  Definition R (A : Set) : Set := stringset -> A.
  Definition ret (A:Set) (a:A) : R A := fun i => a.
  Definition bind (A B:Set) (m : R A) (k : A->R B) : R B :=
     fun r => k (m r) r.
  
  #[global] Instance R_logicVariable : Phoas.LogicVariable (R PL.Exp) :=
    {
    lit i:= ret (PL.Lit i);
    add x y := bind x (fun v1 =>
              bind y (fun v2 =>
              ret (PL.Add v1 v2)))
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
    | Phoas.Exists f =>
        let x := fresh_string_of_set "x" Γ in
        Foas.Exists x
          (phoas_to_foas (union Γ (singleton x))
             (f (ret (PL.Var x))))
    | Phoas.Cmp r a b => Foas.Cmp r (a Γ) (b Γ)
    end.


   Definition example : Foas.prop  := Foas.Forall "x" 
                                                
                                                 (Foas.Cmp SmallerThan (PL.Lit 0%Z) (PL.Var "x")).
     

  

     Definition exampleInverse : phoas_to_foas ∅ (@foas_to_phoas (R PL.Exp) R_logicVariable (empty : stringmap (R PL.Exp)) example ) = example.
     Proof.
     
     vm_compute. reflexivity.  
     Qed.
     Set Printing Implicit.

     

   
End Phoas.
