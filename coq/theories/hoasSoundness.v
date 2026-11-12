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
    pose proof (Hoas.preserves_semantics (vcg.wp PL.valueLogicVariable body
              (vcg.ignore_map
                (λ result : PL.Value,
                    Hoas.hoas_to_phoas (post inp result)))
              {[param := inp]})).

    
    rewrite H4 in H1.
    exact H1.        
    - intros. exact H2.

  Qed.
  
  End Hoas_Sound.
