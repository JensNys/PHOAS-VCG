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

From Phoas Require Import programmingLanguage.

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
        match PL.interp_to_va_crash PL.valueLogicVariable store e1,
              PL.interp_to_va_crash PL.valueLogicVariable store e2 with
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
