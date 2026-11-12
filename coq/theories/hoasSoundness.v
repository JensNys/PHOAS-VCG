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

From Phoas Require Import programmingLanguage foas phoas hoas vcGen.

(* The HOAS verification condition is sound w.r.t. the operational semantics *)

  Section Hoas_Sound.


  




  (*wp is a precondition*)
  (* If the generated weakest precondition holds, running the program will yield a result for wich the postcondition holds.  *)
  (* It might be better to prove this for wp with arbitrary input and map and applying here for a better induction hypothesis  *)
  Lemma wpPreconditionHoas : forall  (post : PL.Value->Hoas.prop) (stm : PL.Stm)  (inp : PL.Value) (arg : string) result fname,       
  (Phoas.semant (vcg.wp PL.valueLogicVariable stm (vcg.ignore_map (Hoas.hoas_to_phoas ∘  post)) {[arg := inp]})) 
  ->
  (PL.evalProg (PL.Fun fname arg stm ) inp result)-> Hoas.semant (post result ).
  Proof.
  Admitted. (*if pre is a precondition*)
  




  

  (* when the vc returns a hoas proposition, it's correct wrt operational semantics of the Hoas contract *)
  Lemma adequate (c : Hoas.Contract) :
   Hoas.semant (vcg.vc_just_hoas c) ->  Hoas.contract_semant c.
  Proof.
  unfold Hoas.contract_semant.
  intros Hvc pre prog post Heq inp result Hpre Heval.
  subst c.
  destruct prog as [functionName param body].
  simpl in Hvc.
  specialize (Hvc inp Hpre).
  apply (@wpPreconditionHoas (post inp) body inp param result functionName).
  - apply Hoas.preserves_semantics. exact Hvc.
  - exact Heval.
  Qed.

  End Hoas_Sound.
