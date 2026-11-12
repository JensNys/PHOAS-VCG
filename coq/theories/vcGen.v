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

From Phoas Require Import programmingLanguage foas phoas hoas.

Module vcg.
Definition Wstore (V A:Set) := (A -> stringmap V -> Phoas.prop V) -> stringmap V -> Phoas.prop V.



  Definition ret (V A:Set) (a:A) : Wstore V A := fun post store => post a store.
  Definition bind (V A B:Set) (c : Wstore V A) (k : A->Wstore V B) : Wstore V B :=
  fun post store1 => c (fun a store2 => (k a) post store2) store1.

  Definition lookupWstore (V : Set)  (varname : string) : Wstore V V :=
  fun post store => match (lookup varname store) with 
                        | None => Phoas.F V
                        | Some value => post value store
                    end.

  Definition lookupWstore_safe (V : Set)  (varname : string) : Wstore V (option V) :=
  fun post store => post (lookup varname store) store.

  Definition insertWstore (V : Set)  (varname : string) (v:V) : Wstore V unit  :=
  fun post store => post tt (insert varname v store).

  Definition deleteWstore (V : Set)  (varname : string) : Wstore V unit  :=
  fun post store => post tt (delete varname store).

  Definition restoreWstore (V : Set)  (varname : string) (oldvalue : option V) : Wstore V unit  :=
  match oldvalue with
  | None => deleteWstore varname
  | Some v => insertWstore varname v
  end.

  Fixpoint exec_exp (V:Set) (VA : PL.LogicVariable V) (e : PL.Exp) : (Wstore V V):= 
  match e with
  | PL.Lit n => ret (VA.(PL.lit) n)
  | PL.Var x => lookupWstore x
  | PL.Add e1 e2 => bind (exec_exp VA e1)  (fun x =>
                    bind (exec_exp VA e2)  (fun y =>
                    ret (VA.(PL.add) x y)
  
  ))
  end.

  Fixpoint exec_stm (V:Set) (VA : PL.LogicVariable V) (stm : PL.Stm) : (Wstore V V):= 
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

  Definition wp (V:Set) (VA : PL.LogicVariable V) (stm : PL.Stm) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.

  Definition ignore_map (V:Set) (post : V->Phoas.prop V) : V->stringmap V->Phoas.prop V :=
  fun result _ => post result.
  
  Fixpoint vc (V:Set) (VA : PL.LogicVariable V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | Phoas.ForallC f => Phoas.Forall (fun v => vc VA (f v))
    | Phoas.HoareTriple pre prog arg post =>
      match prog with 
        | PL.Fun functionName param body => (Phoas.Implies (pre) (wp VA body (ignore_map post) ({[ param := arg ]})))
      end
  end.

  Definition vc_hoas (c : Foas.Contract) : Hoas.prop :=
  Hoas.phoas_to_hoas (vc (PL.valueLogicVariable) ((Phoas.foas_contract_to_phoas_contract PL.valueLogicVariable  ∅ c))).
  
  Definition vc_foas (c : Foas.Contract) : Foas.prop :=
  Phoas.phoas_to_foas ∅ (vc Phoas.R_logicVariable (Phoas.foas_contract_to_phoas_contract Phoas.R_logicVariable  ∅ c)).


  Definition vc_just_hoas (c : Phoas.Contract PL.Value) : Hoas.prop :=
  Hoas.phoas_to_hoas (vc (PL.valueLogicVariable) c).
  
  Lemma vc_hoas_unfold: forall (c  : Foas.Contract ), vc_hoas c = vc_just_hoas (Phoas.foas_contract_to_phoas_contract PL.valueLogicVariable  ∅ c).
  Proof.
  intros. 
  reflexivity.
  Qed. 

End vcg.
