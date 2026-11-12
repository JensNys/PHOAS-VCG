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


(* Defines the syntax and semantics for the object language. The semantics is given both by a big step semantics relation and an interpreter.
Logic Variables are also introduced, which are a way of making expressions with more arbitrary types*)
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
  
  Class LogicVariable (V: Set) :=
  {
  lit : PL.Value -> V;
  add : V -> V -> V;
  cmp : Relop -> V -> V -> Prop
  }.
  
  #[global] Instance valueLogicVariable : LogicVariable (PL.Value) :=
  {
  lit := id;
  add := Z.add;
  cmp := semant_Relop
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






  Fixpoint interp_to_va_default (V : Set) (VA: LogicVariable V) (store:stringmap V) (e : Exp)  : V :=
    match e with
      |Lit n => lit n
      
      |Var x => match (lookup x store) with
                                          | None => lit 0%Z
                                          | Some v => v
                                       end

      | Add l r=> add (interp_to_va_default VA store l) (interp_to_va_default VA store r)
    end.
    
    Fixpoint interp_to_va_crash (V : Set) (VA: LogicVariable V) (store:stringmap V) (e : Exp) : option V :=
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

  (* expressions are compared by evaluating them as closed expressions,
     like comparisons in [Foas.semant'] *)
  #[global] Instance expLogicVariable : LogicVariable PL.Exp :=
  {
  lit := PL.Lit;
  add := PL.Add;
  cmp r e1 e2 := match interp_to_va_crash valueLogicVariable ∅ e1,
                       interp_to_va_crash valueLogicVariable ∅ e2 with
                 | Some v1, Some v2 => semant_Relop r v1 v2
                 | _, _ => False
                 end
  }.

    
  
  
                                           
    
    
      

End PL.
