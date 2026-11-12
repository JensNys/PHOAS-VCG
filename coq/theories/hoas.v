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

From Phoas Require Import programmingLanguage foas phoas.

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

  (* the HOAS contract of a FOAS contract: the logic variables become meta-level values *)
  Definition foas_contract_to_hoas_contract (c : Foas.Contract) : Contract :=
    match c with
    | Foas.MkContract forallVar pre prog arg result post =>
        ForallC (fun v =>
          HoareTriple (phoas_to_hoas (Phoas.foas_to_phoas PL.valueLogicVariable {[ forallVar := v ]} pre))
            prog v
            (fun r => phoas_to_hoas (Phoas.foas_to_phoas PL.valueLogicVariable ({[ forallVar := v ]} ∪ {[ result := r ]}) post)))
    end.




  Lemma inverse_formula (p: Phoas.prop PL.Value) : hoas_to_phoas (phoas_to_hoas p) = p.
  Proof.
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
  Proof.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl. f_equal. unfold "∘".  extensionality v. apply H.
  - simpl. reflexivity.
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
