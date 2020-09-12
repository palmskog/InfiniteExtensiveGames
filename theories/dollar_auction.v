(* Time-stamp: "modifie le 28 Dec 2010 a 07:19 par Pierre Lescanne on boucherotte" *)
(********************************************************************************)
(*                          dollar_auction.v                                    *)
(*                                                                          	*)
(**            © Pierre Lescanne  (February 2008)            	                *)
(*                                                                          	*)
(*		       LIP (ENS-Lyon, CNRS, INRIA) 				*)
(*                                                                          	*)
(*                                                                          	*)
(** Developed in V8.1                                        June-August  2009  *)
(********************************************************************************)
Section dollar_auction.

        (*  ---------------  *)
        (** * Preliminaries  *)
        (*  ---------------  *)


Set Implicit Arguments.
Require Import Relations.
Require Import Arith.
Require Import Omega.
Require Import Even.
Require Import Div2.
(* begin hide *) 
Add LoadPath ".". 
(* end hide *)
Require Import infinite_extensive_games.
Require Import Le.

Implicit Arguments sLeaf [Agent Utility].
Implicit Arguments sNode [Agent Utility].
Implicit Arguments s2u [Agent Utility].
Implicit Arguments LeadsToLeaf [Agent Utility].
Implicit Arguments AlwLeadsToLeaf [Agent Utility].
Implicit Arguments SGPE [Agent Utility].
Implicit Arguments NashEq [Agent Utility]. 

        (*  -----------------  *)
        (** -  Data and tools  *)
        (*  -----------------  *)

Inductive Alice_Bob :Set :=  Alice :Alice_Bob | Bob: Alice_Bob.

Notation "s1 |-- a --| s2" := (IndAgentConv Alice_Bob nat a s1 s2) (at level 70).
Notation "<< a , c , sl , sr >>" := (sNode a c sl sr) (at level 80).
Notation "<< f >>" := (sLeaf f) (at level 80).
Notation "[ x , y ]" := 
  (sLeaf (fun a:Alice_Bob => match a with Alice => x | Bob => y end)) (at level 80).

(** NeverLeaf *)

CoInductive NeverLeaf: StratProf Alice_Bob nat -> Prop :=
|  NvLLeft: forall (a:Alice_Bob) (sl sr: StratProf Alice_Bob nat), NeverLeaf sl -> NeverLeaf (<<a,l,sl,sr>>)
|  NvLRight: forall (a:Alice_Bob) (sl sr: StratProf Alice_Bob nat), NeverLeaf sr -> NeverLeaf (<<a,r,sl,sr>>).

Lemma NLLeft: forall (a:Alice_Bob) (sl sr: StratProf Alice_Bob nat), NeverLeaf (<<a,l,sl,sr>>) -> NeverLeaf sl.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma NLRight: forall (a:Alice_Bob) (sl sr: StratProf Alice_Bob nat), NeverLeaf (<<a,r,sl,sr>>) -> NeverLeaf sr.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma NeverLeaf_then_not_LeadsToLeaf: forall s: StratProf Alice_Bob nat,
  NeverLeaf s -> ~LeadsToLeaf s.
Proof.
unfold not.
intros s H_NL.
induction 1.
inversion H_NL.
apply IHLeadsToLeaf.
apply NLLeft with (a:=a) (sr:=sr).
assumption.
apply IHLeadsToLeaf.
apply NLRight with (a:=a) (sl:=sl).
assumption.
Qed.


        (* ===================== *)
        (** * Dollar auction     *)
        (* ===================== *)



Variable v:nat.

Axiom v_pos: v > 0.

(*  This game is more realistically associated with the dollar auction game 

    A ------- B -------- A ------- B ------- A -------- B ---...
    |         |          |         |         |          |
    |         |          |         |         |          |
 =  |         |          |         |         |          |    ...
    |         |          |         |         |          |
    |         |          |         |         |          |
    
  v+n        n+1       v+n+1      n+2       v+n+2      n+3 
   n         v+n        n+1      v+n+1      n+2       v+n+2

v is the value of the object.

*)


(* -------------------------------- *)
(** ** Alice continues, Bob stops *)
(* -------------------------------- *)

Definition add_Alice_Bob_dol (cA cB:Choice) (n:nat) (s:StratProf Alice_Bob nat) :=
  <<Alice,cA,<<Bob, cB,s,[n+1, v+n]>>,[v+n,n]>>.

CoFixpoint dolAcBs (n:nat): StratProf Alice_Bob nat := add_Alice_Bob_dol l r n (dolAcBs (n+1)).

Lemma dolAcBs_decomposition: forall n:nat,
  (dolAcBs n) = <<Alice,l,<<Bob, r, (dolAcBs (n+1)),[n+1, v+n]>>,[v+n,n]>>.
Proof.
intros.
replace (dolAcBs n) with (StratProf_identity Alice_Bob nat (dolAcBs n)).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Lemma AlwLeadsToLeaf_dolAcBs:  forall (n:nat), AlwLeadsToLeaf (dolAcBs n).
Proof.
cofix H.
intros.
replace (dolAcBs n) with (StratProf_identity Alice_Bob nat (dolAcBs n)).
simpl.
apply ALtL.
apply LtLLeft.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply H.
apply ALtLeaf.
apply ALtLeaf.
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma LeadsToLeaf_dolAcBs: forall (n:nat), LeadsToLeaf (dolAcBs n).
Proof.
intros.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_dolAcBs.
Qed.


Lemma S2u_dolAcBs_Alice: forall (n:nat), s2u (dolAcBs n) Alice (n+1).
Proof.
intros; replace (dolAcBs n) with (StratProf_identity Alice_Bob nat (dolAcBs n)).
simpl.
apply s2uLeft.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => n + 1
         | Bob => v + n
         end)(a:=Alice).
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma S2u_dolAcBs_Bob: forall (n:nat), s2u  (dolAcBs n) Bob (v+n).
Proof.
intros; replace (dolAcBs n) with (StratProf_identity Alice_Bob nat (dolAcBs n)).
simpl.
apply s2uLeft.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => n + 1
         | Bob => v+n
         end)(a:=Bob).
rewrite <- StratProf_decomposition; trivial.
Qed.

Theorem SGPE_dol_Ac_Bs:  forall (n:nat), SGPE ge (dolAcBs n).
Proof.
cofix H.
intros n.
replace (dolAcBs n) with (StratProf_identity Alice_Bob nat (dolAcBs n)).
simpl. 
apply SGPE_left with (u:= n+1) (v:=v+n).
apply ALtL.
apply LtLLeft.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply AlwLeadsToLeaf_dolAcBs.
apply ALtLeaf.
apply ALtLeaf.
apply SGPE_right with (u:= v+(n+1)) (v:=v+n).
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply AlwLeadsToLeaf_dolAcBs.
apply ALtLeaf.
apply H.
apply SGPE_leaf.
apply S2u_dolAcBs_Bob.
apply s2uLeaf with (a:=Bob)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => n+1
         | Bob => v+n
         end).
omega.
apply SGPE_leaf.
apply s2uRight.
apply s2uLeaf with (a:=Alice)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => n + 1
         | Bob => v+n
         end).
apply s2uLeaf with (a:=Alice)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => v + n
         | Bob => n
         end).
cut (v>0).
omega.
apply v_pos.
rewrite <- StratProf_decomposition; trivial.
Qed.


(* ------------------------------- *)
(** ** Alice stops, Bob continues *)
(* ------------------------------- *)

CoFixpoint dolAsBc (n:nat): StratProf Alice_Bob nat := add_Alice_Bob_dol r l n (dolAsBc (n+1)).

Lemma dolAsBc_decomposition: forall n:nat,
  (dolAsBc n) = <<Alice,r,<<Bob, l, (dolAsBc (n+1)),[n+1, v+n]>>,[v+n,n]>>.
Proof.
intros.
replace (dolAsBc n) with (StratProf_identity Alice_Bob nat (dolAsBc n)).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Lemma AlwLeadsToLeaf_dolAsBc:  forall (n:nat), AlwLeadsToLeaf (dolAsBc n).
Proof.
cofix H.
intros.
replace (dolAsBc n) with (StratProf_identity Alice_Bob nat (dolAsBc n)).
simpl.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLLeft.
replace (dolAsBc (n+1)) with (StratProf_identity Alice_Bob nat (dolAsBc (n+1))).
simpl.
apply LtLRight.
apply LtLLeaf.
rewrite <- StratProf_decomposition; trivial.
apply H. 
apply ALtLeaf.
apply ALtLeaf.
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma LeadsToLeaf_dolAsBc: forall (n:nat), LeadsToLeaf (dolAsBc n).
Proof.
intros.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_dolAsBc.
Qed.

Lemma S2u_dolAsBc_Alice: forall (n:nat), s2u (dolAsBc n) Alice (v+n).
Proof.
intros; replace (dolAsBc n) with (StratProf_identity Alice_Bob nat (dolAsBc n)).
simpl.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => v+n
         | Bob => n
         end)(a:=Alice).
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma S2u_dolAsBc_Bob: forall (n:nat), s2u  (dolAsBc n) Bob n.
Proof.
intros; replace (dolAsBc n) with (StratProf_identity Alice_Bob nat (dolAsBc n)).
simpl.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => v+n
         | Bob => n
         end)(a:=Bob).
rewrite <- StratProf_decomposition; trivial.
Qed.

Theorem SGPE_dol_As_Bc:  forall (n:nat), SGPE ge (dolAsBc n).
Proof.
cofix H.
intros n.
replace (dolAsBc n) with (StratProf_identity Alice_Bob nat (dolAsBc n)).
simpl. 
apply SGPE_right with (u:= v+(n+1)) (v:=v+n).
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLLeft.
apply LeadsToLeaf_dolAsBc.
apply AlwLeadsToLeaf_dolAsBc.
apply ALtLeaf.
apply ALtLeaf.
apply SGPE_left with (u:= (n+1)) (v:=v+n).
apply ALtL.
apply LtLLeft.
apply LeadsToLeaf_dolAsBc.
apply AlwLeadsToLeaf_dolAsBc.
apply ALtLeaf.
apply H.
apply SGPE_leaf.
apply S2u_dolAsBc_Bob.
apply s2uLeaf with (a:=Bob)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => n+1
         | Bob => v+n
         end).
cut (v>0).
omega.
apply v_pos.
apply SGPE_leaf.
apply s2uLeft.
apply S2u_dolAsBc_Alice.
apply s2uLeaf with (a:=Alice)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => v+n
         | Bob => n
         end).
cut (v>0).
omega.
apply v_pos.
rewrite <- StratProf_decomposition; trivial.
Qed.

(* ------------------------------- *)
(** **    Alice stops, Bob stops   *)
(* ------------------------------- *)

CoFixpoint dolAsBs (n:nat): StratProf Alice_Bob nat := add_Alice_Bob_dol r r n (dolAsBs (n+1)).

Lemma dolAsBs_decomposition: forall n:nat,
  (dolAsBs n) = <<Alice,r,<<Bob, r, (dolAsBs (n+1)),[n+1, v+n]>>,[v+n,n]>>.
Proof.
intros.
replace (dolAsBs n) with (StratProf_identity Alice_Bob nat (dolAsBs n)).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Lemma AlwLeadsToLeaf_dolAsBs:  forall (n:nat), AlwLeadsToLeaf (dolAsBs n).
Proof.
cofix H.
intros.
replace (dolAsBs n) with (StratProf_identity Alice_Bob nat (dolAsBs n)).
simpl.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply H. 
apply ALtLeaf.
apply ALtLeaf.
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma LeadsToLeaf_dolAsBs: forall (n:nat), LeadsToLeaf (dolAsBs n).
Proof.
intros.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_dolAsBs.
Qed.

Lemma S2u_dolAsBs_Alice: forall (n:nat), s2u (dolAsBs n) Alice (v+n).
Proof.
intros; replace (dolAsBs n) with (StratProf_identity Alice_Bob nat (dolAsBs n)).
simpl.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => v+n
         | Bob => n
         end)(a:=Alice).
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma S2u_dolAsBs_Bob: forall (n:nat), s2u  (dolAsBs n) Bob n.
Proof.
intros; replace (dolAsBs n) with (StratProf_identity Alice_Bob nat (dolAsBs n)).
simpl.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => v+n
         | Bob => n
         end)(a:=Bob).
rewrite <- StratProf_decomposition; trivial.
Qed.

Definition dolAsBs_0' :=  add_Alice_Bob_dol l r 0 (dolAsBs 1).

Lemma conv_dolAsBs: dolAsBs_0' |-- Alice --| dolAsBs 0.
Proof.
replace (dolAsBs 0) with (StratProf_identity Alice_Bob nat (dolAsBs 0)).
unfold  dolAsBs_0'.
unfold  add_Alice_Bob_dol.
simpl.
apply ConvAgent.
apply ConvRefl.
apply ConvRefl.
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma LeadsToLeaf_dolAsBs_0':LeadsToLeaf dolAsBs_0'.
Proof.
unfold  dolAsBs_0'.
unfold  add_Alice_Bob_dol.
simpl.
apply LtLLeft.
apply LtLRight.
apply LtLLeaf.
Qed.

Lemma S2u_dolAsBs_0'_Alice:  s2u dolAsBs_0' Alice 1.
Proof.
intros.
unfold  dolAsBs_0'.
unfold  add_Alice_Bob_dol.
apply s2uLeft. 
apply s2uRight.
apply s2uLeaf with (f:= fun a : Alice_Bob => match a with
                           | Alice => 0 + 1
                           | Bob => v + 0
                           end)(a:=Alice).
Qed.

Theorem NotSGPE_dolAsBs: (v>1) -> ~(NashEq ge (dolAsBs 0)).
Proof.
unfold not.
unfold NashEq.
intros.
cut (1 >= v).
omega.
apply H0 with (a:=Alice)(s':=dolAsBs_0').
apply conv_dolAsBs.
apply S2u_dolAsBs_0'_Alice.
replace v with (v+0).
apply S2u_dolAsBs_Alice.
auto.
Qed.

(* ---------------------------------- *)
(** ** Alice continues, Bob continues *)
(* ---------------------------------- *)

CoFixpoint dolAcBc (n:nat): StratProf Alice_Bob nat := add_Alice_Bob_dol l l n (dolAcBc (n+1)).

Lemma dolAcBc_decomposition: forall n:nat,
  (dolAcBc n) = <<Alice,l,<<Bob, l, (dolAcBc (n+1)),[n+1, v+n]>>,[v+n,n]>>.
Proof.
intros.
replace (dolAcBc n) with (StratProf_identity Alice_Bob nat (dolAcBc n)).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Lemma NeverLeaf_AcBc: forall (n:nat),  NeverLeaf (dolAcBc n).
Proof.
cofix H.
intros.
rewrite  dolAcBc_decomposition.
apply NvLLeft.
apply NvLLeft.
apply H.
Qed.

Lemma Not_LeadsToLeaf_AcBc: forall (n:nat),  ~LeadsToLeaf (dolAcBc n).
Proof.
intros.
apply NeverLeaf_then_not_LeadsToLeaf.
apply  NeverLeaf_AcBc.
Qed.

Lemma NotSGPE_dolAcBc: forall (n:nat), ~SGPE  ge (dolAcBc n).
Proof.
unfold not.
intros.
elim Not_LeadsToLeaf_AcBc with (n:=n).
apply ALtL_then_LtL.
apply SGPE_then_AlwLeadsToLeaf with (preference:=ge).  
assumption.
Qed.

End dollar_auction.
