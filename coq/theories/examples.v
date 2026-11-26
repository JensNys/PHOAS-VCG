From Stdlib Require Import ZArith.ZArith Strings.String.
From stdpp Require Import options stringmap.

From Phoas Require Import programmingLanguage foas phoas vcGen vcgWellFormed.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* Example programs in the object language. *)
Module Examples.

  (* succ(x) = let one = 1 in x + one *)
  Definition succ : PL.Prog :=
    PL.Fun "succ" "x"
      (PL.Let "one" (PL.Lit 1)
         (PL.Expr (PL.Add (PL.Var "x") (PL.Var "one")))).


  Definition example : Foas.prop :=
  Foas.Forall "x" (Foas.Cmp SmallerThan (PL.Var "x") (PL.Add (PL.Var "x") (PL.Lit 0))).

  (* a PHOAS proposition that is generic in the type of logic variables V:
     forall x, x <= x + 1 *)
  Definition phoas_example {V : Set} `{Phoas.LogicVariable V} : Phoas.prop V :=
    Phoas.Forall (fun x => Phoas.Cmp SmallerThanEqual x (Phoas.add x (Phoas.lit 1))).

  (* instantiated with readers it becomes a FOAS proposition *)
  Compute Phoas.phoas_to_foas ∅ phoas_example.

  (* instantiated with values it has a semantics *)
  Example phoas_example_holds : Phoas.semant (V := PL.Value) phoas_example.
  Proof. cbn. intros v. unfold semant_Relop. lia. Qed.
  


  (* forall x, True -> succ(x) = result -> result > x *)
  Definition succ_contract : Foas.Contract :=
    Foas.MkContract "x" Foas.T succ "x" "result"
      (Foas.Cmp GreaterThan (PL.Var "result") (PL.Var "x")).



  Compute vcg.vc_foas succ_contract.

  Example succ_vc : Foas.semant (vcg.vc_foas succ_contract).
  Proof.
    change (vcg.vc_foas succ_contract) with
      (Foas.Forall "x" (Foas.Implies Foas.T
         (Foas.Cmp GreaterThan (PL.Add (PL.Var "x") (PL.Lit 1)) (PL.Var "x")))).
    unfold Foas.semant; cbn. intros arg _.
    rewrite lookup_insert_eq. cbn. lia.
  Qed.




End Examples.
