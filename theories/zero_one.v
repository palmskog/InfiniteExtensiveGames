(* Time-stamp: "modifie le 28 Dec 2010 a 19:30 par Pierre Lescanne on boucherotte" *)
(* **************************************************************************** *)
(*                                zero_one.v                                    *)
(*                                                                          	*)
(*             copyright Pierre Lescanne  (January 2011)            	        *)
(*                                                                          	*)
(*		       LIP (ENS-Lyon, CNRS, INRIA) 				*)
(*                                                                          	*)
(*                                                                          	*)
(* Developed in V8.1                                                Jan  2010   *)
(* **************************************************************************** *)

        (*  ---------------  *)
        (** * Preliminaries  *)
        (*  ---------------  *)

Set Implicit Arguments.

Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Even.
Require Import Div2.
Require Import Le.

Require Import infinite_extensive_games.
Require Import dollar_auction.

Arguments sLeaf [Agent Utility].
Arguments sNode [Agent Utility].
Arguments s2u [Agent Utility].
Arguments LeadsToLeaf [Agent Utility].
Arguments AlwLeadsToLeaf [Agent Utility].
Arguments SGPE [Agent Utility].
Arguments NashEq [Agent Utility]. 
Arguments gLeaf [Agent Utility].
Arguments gNode [Agent Utility].
Arguments s2g [Agent Utility].

        (*  -----------------  *)
        (** -  Data and tools  *)
        (*  -----------------  *)

(* Inductive Alice_Bob :Set :=  Alice :Alice_Bob | Bob: Alice_Bob.*)

Notation "s1 |-- a --| s2" := (IndAgentConv Alice_Bob nat a s1 s2) (at level 70).
Notation "<< a , c , sl , sr >>" := (sNode a c sl sr) (at level 80).
Notation "<< f >>" := (sLeaf f) (at level 80).
Notation "[ x , y ]" := 
  (sLeaf (fun a:Alice_Bob => match a with Alice => x | Bob => y end)) (at level 80).
Notation "[[ x , y ]]" := 
  (gLeaf (fun a:Alice_Bob => match a with Alice => x | Bob => y end)) 
      (at level 80).
Notation "g =gbis= g'" := (gBisimilar Alice_Bob nat g g') (at level 80).


(* ---------------------------------- *)
(** ** Infinite Game Zero One        *)
(* ---------------------------------- *)
Definition add_Alice_Bob_zero_one_game (g:Game Alice_Bob nat) :=
gNode Alice (gNode Bob g ([[0, 1]])) ([[1,0]]).

CoFixpoint zero_one_game: Game Alice_Bob nat:= 
  add_Alice_Bob_zero_one_game zero_one_game.

Lemma zero_one_game_decomposition: 
    gNode Alice (gNode Bob zero_one_game ([[0, 1]])) ([[1,0]]) = 
        zero_one_game.
Proof.
pattern zero_one_game at 2.
replace zero_one_game with  (Game_identity Alice_Bob nat zero_one_game).
simpl.
apply refl_equal.
apply Game_decomposition.
Qed.

Definition add_Alice_Bob_zero_one_strat (cA cB:Choice) (s:StratProf Alice_Bob nat) :=
  <<Alice,cA,<<Bob, cB,s,[0, 1]>>,[1,0]>>.

(* -------------------------------- *)
(** ** Alice continues, Bob stops *)
(* -------------------------------- *)

CoFixpoint z1AcBs: StratProf Alice_Bob nat := add_Alice_Bob_zero_one_strat l r z1AcBs.

Lemma z1AcBs_decomposition: <<Alice,l,<<Bob, r, z1AcBs,[0,1]>>,[1,0]>> = z1AcBs.
Proof.
pattern z1AcBs at 2.
replace z1AcBs with (StratProf_identity Alice_Bob nat z1AcBs).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Lemma AlwLeadsToLeaf_z1AcBs:  AlwLeadsToLeaf z1AcBs.
Proof.
cofix H.
replace z1AcBs with (StratProf_identity Alice_Bob nat z1AcBs).
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

Lemma LeadsToLeaf_z1AcBs: LeadsToLeaf z1AcBs.
Proof.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_z1AcBs.
Qed.

Lemma S2u_z1AcBs_Alice: s2u z1AcBs Alice 0.
Proof.
intros; replace z1AcBs with (StratProf_identity Alice_Bob nat z1AcBs).
simpl.
apply s2uLeft.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => 0
         | Bob => 1
         end)(a:=Alice).
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma S2u_z1AcBs_Bob: s2u  z1AcBs Bob 1.
Proof.
intros; replace z1AcBs with (StratProf_identity Alice_Bob nat z1AcBs).
simpl.
apply s2uLeft.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => 0
         | Bob => 1
         end)(a:=Bob).
rewrite <- StratProf_decomposition; trivial.
Qed.

Theorem SGPE_zero_one_Ac_Bs: SGPE ge z1AcBs.
Proof.
cofix H.
replace z1AcBs with (StratProf_identity Alice_Bob nat z1AcBs).
simpl. 
apply SGPE_left with (u:= 0) (v:=1).
apply ALtL.
apply LtLLeft.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply AlwLeadsToLeaf_z1AcBs.
apply ALtLeaf.
apply ALtLeaf.
apply SGPE_right with (u:= 1) (v:=1).
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply AlwLeadsToLeaf_z1AcBs.
apply ALtLeaf.
apply H.
apply SGPE_leaf.
apply S2u_z1AcBs_Bob.
apply s2uLeaf with (a:=Bob)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => 0
         | Bob => 1
         end).
lia.
apply SGPE_leaf.
apply s2uRight.
apply s2uLeaf with (a:=Alice)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => 0
         | Bob => 1
         end).
apply s2uLeaf with (a:=Alice)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => 1
         | Bob => 0
         end).
lia.
rewrite <- StratProf_decomposition; trivial.
Qed.

(* ------------------------------- *)
(** ** Alice stops, Bob continues *)
(* ------------------------------- *)

CoFixpoint z1AsBc: StratProf Alice_Bob nat := add_Alice_Bob_zero_one_strat r l z1AsBc.

Lemma z1AsBc_decomposition: z1AsBc = <<Alice,r,<<Bob, l, z1AsBc,[0, 1]>>,[1,0]>>.
Proof.
intros.
pattern z1AsBc at 1.
replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Lemma AlwLeadsToLeaf_z1AsBc: AlwLeadsToLeaf z1AsBc.
Proof.
cofix H.
replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl.
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLLeft.
replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl.
apply LtLRight.
apply LtLLeaf.
rewrite <- StratProf_decomposition; trivial.
apply H. 
apply ALtLeaf.
apply ALtLeaf.
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma LeadsToLeaf_z1AsBc: LeadsToLeaf z1AsBc.
Proof.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_z1AsBc.
Qed.

Lemma S2u_z1AsBc_Alice: s2u z1AsBc Alice 1.
Proof.
intros; replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => 1
         | Bob => 0
         end)(a:=Alice).
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma S2u_z1AsBc_Bob: s2u  z1AsBc Bob 0.
Proof.
intros; replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl.
apply s2uRight.
apply s2uLeaf with (f:=fun a : Alice_Bob =>
         match a with
         | Alice => 1
         | Bob => 0
         end)(a:=Bob).
rewrite <- StratProf_decomposition; trivial.
Qed.

Theorem SGPE_zero_one_As_Bc:  SGPE ge z1AsBc.
Proof.
cofix H.
replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl. 
apply SGPE_right with (u:= 1) (v:= 1).
apply ALtL.
apply LtLRight.
apply LtLLeaf.
apply ALtL.
apply LtLLeft.
apply LeadsToLeaf_z1AsBc.
apply AlwLeadsToLeaf_z1AsBc.
apply ALtLeaf.
apply ALtLeaf.
apply SGPE_left with (u:= 0) (v:=1).
apply ALtL.
apply LtLLeft.
apply LeadsToLeaf_z1AsBc.
apply AlwLeadsToLeaf_z1AsBc.
apply ALtLeaf.
apply H.
apply SGPE_leaf.
apply S2u_z1AsBc_Bob.
apply s2uLeaf with (a:=Bob)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => 0
         | Bob => 1
         end).
lia.
apply SGPE_leaf.
apply s2uLeft.
apply S2u_z1AsBc_Alice.
apply s2uLeaf with (a:=Alice)(f:=fun a : Alice_Bob =>
         match a with
         | Alice => 1
         | Bob => 0
         end).
lia.
rewrite <- StratProf_decomposition; trivial.
Qed.

Lemma s2g_z1AcBs: s2g z1AcBs =gbis= zero_one_game.
Proof.
cofix H.
replace z1AcBs with (<<Alice,l,<<Bob, r, z1AcBs,[0, 1]>>,[1,0]>>).
rewrite s2g_decomp.
rewrite s2g_decomp.
rewrite s2g_leaf.
rewrite s2g_leaf.
rewrite <- zero_one_game_decomposition.
apply bisim_gNode.
apply bisim_gNode.
apply H.
apply bisim_gLeaf.
apply bisim_gLeaf.
pattern z1AcBs at 2.
replace z1AcBs with (StratProf_identity Alice_Bob nat z1AcBs).
simpl.
trivial.
apply z1AcBs_decomposition.
Qed.

Lemma s2g_z1AsBc: s2g z1AsBc =gbis= zero_one_game.
Proof.
cofix H.
replace z1AsBc with (<<Alice,r,<<Bob, l, z1AsBc,[0, 1]>>,[1,0]>>).
rewrite s2g_decomp.
rewrite s2g_decomp.
rewrite s2g_leaf.
rewrite s2g_leaf.
rewrite <- zero_one_game_decomposition.
apply bisim_gNode.
apply bisim_gNode.
apply H.
apply bisim_gLeaf.
apply bisim_gLeaf.
pattern z1AsBc at 2.
replace z1AsBc with (StratProf_identity Alice_Bob nat z1AsBc).
simpl.
trivial.
apply StratProf_decomposition.
Qed.

Definition test_even (n:nat) : {even n} + {odd n}.
elim n.
left.
apply even_O.
intros  m H.
elim H.
right.
apply odd_S. 
assumption.
left.
apply even_S.
assumption.
Defined.

Definition Z1_seq (m:nat) : (Game Alice_Bob nat)  := match test_even m with
| left h => zero_one_game
| right h => (gNode Bob zero_one_game ([[0, 1]]))
end.

Lemma Z1_even_z1AcBs: forall m, even m ->
s2g z1AcBs =gbis= (Z1_seq m).
Proof.
unfold Z1_seq.
intros.
case (test_even m).
intros.
apply s2g_z1AcBs.
intro.
elim not_even_and_odd with (n:=m); trivial.
Qed.

Lemma Z1_even_z1AsBc: forall m, even m ->
s2g z1AsBc =gbis= (Z1_seq m).
Proof.
unfold Z1_seq.
intros.
case (test_even m).
intros.
apply s2g_z1AsBc.
intro.
elim not_even_and_odd with (n:=m); trivial.
Qed.

Lemma Z1_odd_z1AcBs: forall m c, odd m ->
s2g (<<Bob,c,z1AcBs, ([0,1])>>)=gbis=(Z1_seq m).
Proof.
intros.
rewrite s2g_decomp.
rewrite s2g_leaf.
unfold Z1_seq.
case (test_even m).
intros.
elim not_even_and_odd with (n:=m); trivial.
intros.
apply bisim_gNode.
apply s2g_z1AcBs.
apply gBis_refl.
Qed.

Lemma Z1_odd_z1AsBc: forall m c, odd m -> s2g (<<Bob,c,z1AsBc, ([0,1])>>)=gbis=(Z1_seq m).
Proof.
intros.
rewrite s2g_decomp.
rewrite s2g_leaf.
unfold Z1_seq.
case (test_even m).
intros.
elim not_even_and_odd with (n:=m); trivial.
intros.
apply bisim_gNode.
apply s2g_z1AsBc.
apply gBis_refl.
Qed.

Theorem Zero_one_game_has_an_escalation_sequence: 
    has_an_escalation_sequence Alice_Bob nat ge Z1_seq.
Proof.
unfold has_an_escalation. 
intro m.
elim even_odd_dec with (n:=m).
(* case even m*)
intro.
exists (<<Bob, r, z1AcBs, ([0,1])>>).
exists ([1,0]).
exists Alice.
split.
left.
split.
rewrite s2g_decomp.
rewrite s2g_decomp.
rewrite s2g_leaf.
unfold Z1_seq.
case (test_even m).
intros.
rewrite <- zero_one_game_decomposition.
apply bisim_gNode.
apply bisim_gNode.
apply  s2g_z1AcBs.
apply gBis_refl.
rewrite s2g_leaf.
apply gBis_refl.
intros. 
elim not_even_and_odd with (n:=m); trivial.
rewrite z1AcBs_decomposition.
apply SGPE_zero_one_Ac_Bs.
apply Z1_odd_z1AcBs.
replace (m+1) with (S m).
apply odd_S.
trivial.
lia.
(* case odd m *)
intro.
exists z1AsBc.
exists ([0,1]).
exists Bob.
split.
left.
split.
apply Z1_odd_z1AsBc.
trivial.
apply SGPE_left with (u:=0) (v:= 1).
apply ALtL.
apply LtLLeft.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_z1AsBc.
apply AlwLeadsToLeaf_z1AsBc.
apply ALtLeaf.
apply SGPE_zero_one_As_Bc.
apply SGPE_leaf.
apply S2u_z1AsBc_Bob.
apply s2uLeaf with (a:= Bob) (f:= (
    fun a : Alice_Bob =>
    match a with
    | Alice => 0
    | Bob => 1
    end )).
lia.
apply Z1_even_z1AsBc.
replace (m+1) with (S m).
apply even_S.
trivial.
lia.
Qed.

Theorem Zero_one_game_has_an_escalation: 
    has_an_escalation Alice_Bob nat ge zero_one_game.
Proof.
unfold has_an_escalation.
exists Z1_seq.
split.
apply Zero_one_game_has_an_escalation_sequence.
unfold Z1_seq.
case (test_even 0).
trivial.
intros.
elim not_even_and_odd with (n:=0).
apply even_O.
assumption.
Qed.
