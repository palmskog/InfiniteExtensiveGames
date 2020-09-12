(* Time-stamp: "modifie le 28 Dec 2010 a 07:42 par Pierre Lescanne on boucherotte" *)
(* **************************************************************************** *)
(*                  escalation_dollar_auction.v                                 *)
(*                                                                          	*)
(*            copyright Pierre Lescanne  (February 2008)            	        *)
(*                                                                          	*)
(*		       LIP (ENS-Lyon, CNRS, INRIA) 				*)
(*                                                                          	*)
(*                                                                          	*)
(* Developed in V8.1                                        June-August  2009   *)
(* **************************************************************************** *)

        (*  ---------------  *)
        (** * Preliminaries  *)
        (*  ---------------  *)

Require Import Relations.
Require Import Arith.
Require Import Lia.
Require Import Even.
Require Import Div2.
Require Import Le.

Require Import infinite_extensive_games.
Require Import dollar_auction.

Set Implicit Arguments.

Section escalation_dollar_auction.

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
(** ** Escalation for dollar action   *)
(* ---------------------------------- *)

Variable v:nat.
Hypothesis v_pos: v > 0.

Definition add_Alice_Bob_dol_game (n:nat) (g:Game Alice_Bob nat) :=
gNode Alice (gNode Bob g ([[n+1, v+n]])) ([[v+n,n]]).

CoFixpoint dollar_game (n:nat): Game Alice_Bob nat:= 
  add_Alice_Bob_dol_game n (dollar_game (n+1)).

Lemma dollar_game_decomposition: forall n, 
    gNode Alice (gNode Bob (dollar_game (n+1)) ([[n+1, v+n]])) ([[v+n,n]]) = 
        dollar_game n.
Proof.
intros.
replace (dollar_game n) with (Game_identity Alice_Bob nat (dollar_game n)).
simpl.
apply refl_equal.
apply Game_decomposition.
Qed.

Lemma s2g_dolAcBs: forall n, s2g (dolAcBs v n) =gbis= dollar_game n.
Proof.
cofix H.
intro.
replace (dolAcBs v n) with (<<Alice,l,<<Bob, r, (dolAcBs v (n+1)),[n+1, v+n]>>,[v+n,n]>>).
rewrite s2g_decomp.
rewrite s2g_decomp.
rewrite s2g_leaf.
rewrite s2g_leaf.
rewrite <- dollar_game_decomposition.
apply bisim_gNode.
apply bisim_gNode.
apply H.
apply bisim_gLeaf.
apply bisim_gLeaf.
rewrite <- dolAcBs_decomposition.
trivial.
Qed.

Lemma s2g_dolAsBc: forall n, s2g (dolAsBc v n) =gbis= dollar_game n.
Proof.
cofix H.
intro.
replace (dolAsBc v n) with (<<Alice,r,<<Bob, l, (dolAsBc v (n+1)),[n+1, v+n]>>,[v+n,n]>>).
rewrite s2g_decomp.
rewrite s2g_decomp.
rewrite s2g_leaf.
rewrite s2g_leaf.
rewrite <- dollar_game_decomposition.
apply bisim_gNode.
apply bisim_gNode.
apply H.
apply bisim_gLeaf.
apply bisim_gLeaf.
rewrite <- dolAsBc_decomposition.
trivial.
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

Definition DG_seq (m:nat) : (Game Alice_Bob nat)  := match test_even m with
| left h => dollar_game (div2 m)
| right h => (gNode Bob (dollar_game ((div2 m)+1)) 
                        ([[((div2 m)+1), (v+(div2 m))]]))                        
end.

Lemma DG_even_dolAcBs: forall m, even m ->
s2g (dolAcBs v (div2 m)) =gbis= (DG_seq m).
Proof.
unfold DG_seq.
intros.
case (test_even m).
intros.
apply s2g_dolAcBs.
intro.
elim not_even_and_odd with (n:=m); trivial.
Qed.

Lemma DG_even_dolAsBc: forall m, even m ->
s2g (dolAsBc v (div2 m)) =gbis= (DG_seq m).
Proof.
unfold DG_seq.
intros.
case (test_even m).
intros.
apply s2g_dolAsBc.
intro.
elim not_even_and_odd with (n:=m); trivial.
Qed.

Lemma DG_odd_dolAcBs: forall m c, odd m ->
s2g (<<Bob,c,(dolAcBs v (div2 m + 1)), ([div2 m+1,v+(div2 m)])>>)=gbis=(DG_seq m).
Proof.
intros.
rewrite s2g_decomp.
rewrite s2g_leaf.
unfold DG_seq.
case (test_even m).
intros.
elim not_even_and_odd with (n:=m); trivial.
intros.
apply bisim_gNode.
apply s2g_dolAcBs.
apply gBis_refl.
Qed.

Lemma DG_odd_dolAsBc: forall m c, odd m ->
s2g (<<Bob,c,(dolAsBc v (div2 m + 1)), ([div2 m+1,v+(div2 m)])>>)=gbis=(DG_seq m).
Proof.
intros.
rewrite s2g_decomp.
rewrite s2g_leaf.
unfold DG_seq.
case (test_even m).
intros.
elim not_even_and_odd with (n:=m); trivial.
intros.
apply bisim_gNode.
apply s2g_dolAsBc.
apply gBis_refl.
Qed.

Theorem Dollar_game_has_an_escalation_sequence: 
    has_an_escalation_sequence Alice_Bob nat ge DG_seq.
Proof.
unfold has_an_escalation. 
intro m.
elim even_odd_dec with (n:=m).
(* case even m*)
intro.
exists (<<Bob, r, dolAcBs v ((div2 m)+1),
                        ([((div2 m)+1), (v+(div2 m))])>>).
exists ([(v+div2 m), (div2 m)]).
exists Alice.
split.
left.
split.
rewrite s2g_decomp.
rewrite s2g_decomp.
rewrite s2g_leaf.
rewrite s2g_leaf.
unfold DG_seq.
case (test_even m).
intros.
rewrite <- dollar_game_decomposition.
apply bisim_gNode.
apply bisim_gNode.
apply  s2g_dolAcBs.
apply gBis_refl.
apply gBis_refl.
intros. 
elim not_even_and_odd with (n:=m); trivial.
rewrite <- dolAcBs_decomposition.
apply SGPE_dol_Ac_Bs; apply v_pos.
replace (div2 m) with (div2 (m + 1)).
apply DG_odd_dolAcBs.
replace (m+1) with (S m).
apply odd_S.
trivial.
lia.
apply sym_eq.
replace (m+1) with (S m).
apply even_div2.
trivial.
lia.
(* case odd m *)
intro.
exists (dolAsBc v ((div2 m)+1)).
exists ([div2 m + 1,v+(div2 m)]).
exists Bob.
split.
left.
split.
apply DG_odd_dolAsBc.
trivial.
apply SGPE_left with (u:=div2 m+1) (v:= v + div2 m).
apply ALtL.
apply LtLLeft.
apply ALtL_then_LtL.
apply AlwLeadsToLeaf_dolAsBc.
apply AlwLeadsToLeaf_dolAsBc.
apply ALtLeaf.
apply SGPE_dol_As_Bc; apply v_pos.
apply SGPE_leaf.
apply S2u_dolAsBc_Bob.
apply s2uLeaf with (a:= Bob) (f:= (
    fun a : Alice_Bob =>
    match a with
    | Alice => div2 m + 1
    | Bob => v + div2 m
    end )).
cut (v>0).
lia.
apply v_pos.

replace (div2 m +1) with (div2 (m+1)).
apply DG_even_dolAsBc.
replace (m+1) with (S m).
apply even_S.
trivial.
lia.
replace (div2 m +1) with (S (div2 m)).
apply sym_eq.
replace (m+1) with (S m).
apply odd_div2.
trivial.
lia.
lia.
Qed.

Theorem Dollar_game_has_an_escalation: 
    has_an_escalation Alice_Bob nat ge (dollar_game 0).
Proof.
unfold has_an_escalation.
exists DG_seq.
split.
apply Dollar_game_has_an_escalation_sequence.
unfold DG_seq.
case (test_even 0).
trivial.
intros.
elim not_even_and_odd with (n:=0).
apply even_O.
assumption.
Qed.

End escalation_dollar_auction.
