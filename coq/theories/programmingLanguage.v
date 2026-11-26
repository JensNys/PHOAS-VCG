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


Inductive Relop : Set :=
  | Equal
  | GreaterThan
  | SmallerThan
  | GreaterThanEqual
  | SmallerThanEqual.

(* values of the programming language are integers *)
Definition semant_Relop (r:Relop) : Z->Z->Prop :=
    match r with
      |Equal => eq
      |SmallerThan => Z.lt
      |GreaterThan => Z.gt
      |GreaterThanEqual => Z.ge
      |SmallerThanEqual => Z.le
    end.


(* Defines the syntax and semantics for the object language. The semantics is given both by a big step semantics relation and an interpreter.*)
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
  
(* I use big step semantics because it is closer to the interpreter i already have. 
The disadvantage of big step semantics is that it doesn't give a semantics to non-terminating programs. 
Since a contract and it postcondition makes a statement about terminating programs (If a program terminates with result r, {P} program {r.Q} holds). angelic/demonic choice determines whether a contract holds for non-terminating programs by either making the weakest precondition true or false.
therefore in our case i don't think we have a need for a small-step semantics. *)

(* Z_scope only around evalExp: in evalStm, [*] must stay the product type *)
Local Open Scope Z_scope.

(* big step semantics for expressions *)
Inductive evalExp (store : stringmap Value) :
    Exp -> Value -> Prop :=
  | EvalLit n :
      evalExp store (Lit n) n
  | EvalVar x v :
      lookup x store = Some v ->
      evalExp store (Var x) v
  | EvalAdd a b v1 v2 :
      evalExp store a v1 ->
      evalExp store b v2 ->
      evalExp store (Add a b) (v1 + v2).

Local Close Scope Z_scope.

(* big step semantics for statements *)
Inductive evalStm (store : stringmap Value) :
    Stm -> Value * stringmap Value -> Prop :=
  | EvalExpr e v :
      evalExp store e v ->
      evalStm store (Expr e) (v, store)
  | EvalLet x e body v result store' :
      evalExp store e v ->
      evalStm (<[x := v]> store) body (result, store') ->
      evalStm store (Let x e body) (result, delete x store').

(* big step semantics for programs *)
Inductive evalProg : Prog -> Value -> Value -> Prop :=
  | EvalFunc f param body input result store' :
      evalStm {[param := input]} body (result, store') ->
      evalProg (Fun f param body) input result.

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






  (* interpreter for expressions over values; crashes (None) on unbound variables *)
  Fixpoint interp_exp (store : stringmap Value) (e : Exp) : option Value :=
    match e with
    | Lit n => Some n
    | Var x => store !! x
    | Add l r =>
        match interp_exp store l, interp_exp store r with
        | Some lv, Some rv => Some (Z.add lv rv)
        | _, _ => None
        end
    end.

End PL.
