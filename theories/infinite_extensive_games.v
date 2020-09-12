(* Time-stamp: "modifie le 29 Dec 2010 a 19:52 par Pierre Lescanne on boucherotte" *)
(* **************************************************************************** *)
(*                         infinite_extensive_games.v                           *)
(*                                                                          	*)
(*                 copyright Pierre Lescanne  (February 2008)                   *)
(*                                                                          	*)
(*		       LIP (ENS-Lyon, CNRS, INRIA) 				*)
(*                                                                          	*)
(*                                                                          	*)
(* Developed in V8.1                           February 2008 --- January 2009   *)
(* **************************************************************************** *)
Section InfiniteExtensiveGames.

        (*  -------------- *)
        (** - Requirements *)
        (*  -------------- *)

Require Import Relations.
Require Import Omega.
        (** * Agents, utilities, preference, choices *)
Variable Agent : Set.
Variable Utility: Set.
Variable preference: relation Utility.  Infix "=<" := preference (at level 100).
Hypothesis preference_is_preorder: preorder Utility preference.
Hypothesis nonTrivialUtility: exists x: Utility, exists y: Utility, x <> y.
Definition Utility_fun := Agent -> Utility.
Inductive Choice : Set := | l | r. 

        (*  ----------------- *)
        (** *    Histories    *)
        (*  ----------------- *)

CoInductive History: Set :=
| HNil: History
| HCons: Choice -> History -> History.

CoInductive hBisimilar:History  ->History -> Prop :=
| bisim_HNil:hBisimilar HNil HNil
| bisim_HCons: forall (a:Choice)(h h':History),
  hBisimilar h h' -> hBisimilar (HCons a h) (HCons a h').

Definition History_identity (h:History): History :=
match h with
| HNil =>  HNil
| HCons a h => HCons a h
end.

Lemma History_decomposition: forall h: History,
  History_identity h = h.
Proof. 
intros h; case h; trivial.
Qed.

(* notation *) Notation "h =hbis= h'" := (hBisimilar h h') (at level 80).

        (*  -------------- *)
        (** *   Games      *)
        (*  -------------- *)

CoInductive Game : Set :=
| gLeaf:  Utility_fun -> Game
| gNode : Agent -> Game -> Game -> Game.

(** - Tools *)
Lemma Game_Left: forall a a' gl gl' gr gr',
  gNode a gl gr = gNode a' gl' gr' ->  gl = gl'.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma Game_Right: forall a a' gl gl' gr gr',
  gNode a gl gr = gNode a' gl' gr' ->  gr = gr'.
Proof.
intros.
inversion H.
trivial.
Qed.

Definition Game_identity (g:Game): Game :=
match g with
| gLeaf f =>  gLeaf f
| gNode a gl gr => gNode a gl gr
end.

Lemma Game_decomposition: forall g: Game, Game_identity g = g.
Proof. 
intros g; case g; trivial.
Qed.

(** - Finiteness *)
Inductive FiniteGame: Game -> Prop :=
| Fin_gLeaf: forall f:Utility_fun, FiniteGame (gLeaf f)
| Fin_gNode: forall (a:Agent) (gl gr:Game),
     FiniteGame gl ->  FiniteGame gr -> FiniteGame (gNode a gl gr).

(** - Bisimilarity *)
CoInductive gBisimilar: Game -> Game -> Prop :=
| bisim_gLeaf: forall f, gBisimilar (gLeaf f) (gLeaf f)
| bisim_gNode: forall a gl gl' gr gr',
  gBisimilar gl gl' -> gBisimilar gr gr' ->  gBisimilar (gNode a gl gr) (gNode a gl' gr').

(* notation *) Notation "g =gbis= g'" := (gBisimilar g g') (at level 80).

Lemma gBis_refl: forall g, g =gbis= g.
Proof.
cofix H_bref.
intros g.
case g.
apply bisim_gLeaf.
intros.
apply bisim_gNode; apply H_bref.
Qed.

Lemma gBis_sym: forall g g', g =gbis= g' -> g' =gbis= g.
Proof.
cofix H_bref.
intros g g'.
case g.
case g'.
intros; inversion H.
apply bisim_gLeaf.

intros.
inversion H.
intros.
inversion H.
apply bisim_gNode; apply H_bref; assumption.
Qed.

(** - Histories of a game *)
CoInductive IsHistoryOf: History -> Game -> Prop :=
| hist_Leaf: forall (f:Utility_fun), IsHistoryOf HNil (gLeaf f)
| hist_NodeLeft: forall (a:Agent)(gl gr:Game)(h:History), 
    (IsHistoryOf h gl) -> IsHistoryOf (HCons l h) (gNode a gl gr)
| hist_NodeRight: forall (a:Agent)(gl gr:Game)(h:History), 
    (IsHistoryOf h gr) -> IsHistoryOf (HCons r h) (gNode a gl gr).

(* notation *) Notation "h >is_history_of g" := (IsHistoryOf h g) (at level 80).

CoInductive uf_of_h_in_g: Utility_fun -> History -> Game -> Prop :=
| uhgLeaf: forall (f:Utility_fun), uf_of_h_in_g f HNil (gLeaf f)
| uhgLeft: forall (a:Agent)(gl gr:Game)(h:History)(f:Utility_fun), 
    (uf_of_h_in_g f h gl) -> uf_of_h_in_g f (HCons l h) (gNode a gl gr)
| uhgRight: forall (a:Agent)(gl gr:Game)(h:History)(f:Utility_fun), 
    (uf_of_h_in_g f h gr) -> uf_of_h_in_g f (HCons r h) (gNode a gl gr).


        (*  -------------- *)
        (** *  Strategies  *)
        (*  -------------- *)


CoInductive StratProf : Set :=
| sLeaf : Utility_fun -> StratProf
| sNode : Agent -> Choice -> StratProf -> StratProf -> StratProf.

(* Notation *) Notation "<< a , c , sl , sr >>" := (sNode a c sl sr) (at level 80).
    Notation "<< f >>" := (sLeaf f) (at level 80).

(**Go to left, go to right*)
Inductive GoToLeft : StratProf -> Prop :=
|goL : forall (a: Agent) (sl sr : StratProf), GoToLeft (<<a,l,sl,sr>>).
Inductive GoToRight : StratProf -> Prop :=
|goR : forall (a: Agent) (sl sr : StratProf), GoToRight (<<a,r,sl,sr>>).

(** - Tools *)
Lemma StratProf_Leaf: forall f f', <<f>> = (<<f'>>) -> f = f'.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma StratProf_Left: forall a a' c c' sl sl' sr sr',
  (<<a,c,sl,sr>> = <<a',c',sl',sr'>>) -> sl = sl'.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma StratProf_Right: forall a a' c c' sl sl' sr sr',
  (<<a,c,sl,sr>> = <<a',c',sl',sr'>>) -> sr = sr'.
Proof.
intros.
inversion H.
trivial.
Qed.

Definition StratProf_identity (s:StratProf): StratProf :=
match s with
| <<f>> =>  <<f>>
| <<a,c,sl,sr>> => <<a,c,sl,sr>>
end.

Lemma StratProf_decomposition: forall s: StratProf,
  StratProf_identity s = s.
Proof. 
intros s; case s; trivial.
Qed.

(** - Finiteness *)
Inductive FiniteStrat: StratProf -> Prop :=
| Fin_sLeaf: forall f:Utility_fun, FiniteStrat (<<f>>)
| Fin_sNode: forall (a:Agent) (c:Choice) (sl sr:StratProf),
     FiniteStrat sl ->  FiniteStrat sr -> FiniteStrat (<<a,c,sl,sr>>).

CoInductive hasInfiniteHistory:  StratProf -> Prop :=
| InfHistLeft: forall a sl sr, hasInfiniteHistory sl -> hasInfiniteHistory (<<a,l,sl,sr>>)
| InfHistRight: forall a sl sr, hasInfiniteHistory sr -> hasInfiniteHistory (<<a,r,sl,sr>>).

Lemma Finite_notInfinite:  forall s, FiniteStrat s -> ~hasInfiniteHistory s.
Proof.
intros.
elim H.
unfold not.
intros.
inversion H0.
intros.
destruct c.
unfold not.
intros.
inversion H4.  
apply H1. assumption.
unfold not.
intros.
inversion H4.  
apply H3. assumption.
Qed.

Lemma hasInfiniteHistory_NotFinite: forall s, hasInfiniteHistory s -> ~FiniteStrat s.
Proof.
unfold not.
intros s HInf HFin.
generalize HInf.
apply Finite_notInfinite.
assumption.
Qed.

(** - Bisimilarity *)
CoInductive sBisimilar: StratProf -> StratProf -> Prop :=
| bisim_sLeaf: forall f, sBisimilar (<<f>>) (<<f>>)
| bisim_sNode: forall a c sl sl' sr sr',
  sBisimilar sl sl' -> sBisimilar sr sr' ->  sBisimilar (<<a,c,sl,sr>>) (<<a, c,sl',sr'>>).

        (** ** The game of a strategy *)

(** - From strategies to games *)
CoFixpoint s2g (s:StratProf) : Game := 
match s with
|  <<f>> => gLeaf f  
|  <<a,_,sl,sr>> => (gNode a (s2g sl) (s2g sr))
end.

Lemma s2g_decomp: forall a c sl sr,
    s2g (<<a, c, sl, sr>>) = gNode a (s2g sl) (s2g sr).
Proof.
intros.
replace (s2g (<< a, c, sl, sr >>)) with (Game_identity (s2g (<< a, c, sl, sr >>))).
simpl.
trivial.
apply Game_decomposition.
Qed.

Lemma s2g_leaf: forall uf, s2g (sLeaf uf) = gLeaf uf.
Proof.
intros.
replace (s2g (sLeaf uf)) 
  with (Game_identity (s2g (sLeaf uf))).
simpl.
trivial.
apply Game_decomposition.
Qed.

(** - Strategies with bisimilar associated games *)
CoInductive BisGame: StratProf -> StratProf -> Prop :=
| BGLeaf: forall f, BisGame (<<f>>) (<<f>>)
| BGNode: forall (a:Agent)(c c':Choice)(sl sr sl' sr':StratProf), 
  BisGame sl sl' -> BisGame sr sr' -> BisGame (sNode a c sl sr) (sNode a c' sl' sr').

(* Notation *) Notation "s =sbisg= s'":= (BisGame s s') (at level 70).

Lemma BisGame_refl: forall s, s=sbisg=s.
Proof.
cofix H.
intros.
case s.
intros.
apply BGLeaf.
intros.
apply BGNode; apply H. 
Qed.

Lemma BisGame_trans : forall s s' s'': StratProf, BisGame s s' -> BisGame s' s'' -> BisGame s s''.
Proof.
cofix H.
intros s s' s'' s_s' s'_s''.
inversion s_s'; inversion s'_s''.
rewrite H1.
rewrite H2.
apply BisGame_refl.
generalize H4.
rewrite <- H1.
intro absurde.
inversion absurde.
generalize H4.
rewrite <- H3.
intro absurde.
inversion absurde.
generalize H6.
rewrite <- H3.
intro s'_equal_s'.
inversion s'_equal_s'.
apply BGNode.
eapply H.
apply H0. rewrite <- H11. assumption.
eapply H.
apply H1. rewrite <- H12. assumption.
Qed.

Lemma BisGame_revLeft : forall (a: Agent) (sl sl' sr sr' : StratProf) (c c': Choice),
BisGame (<<a, c, sl, sr>>) (<<a, c', sl', sr'>>) -> BisGame sl sl'.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma BisGame_revRight : forall (a: Agent) (sl sl' sr sr' : StratProf) (c c': Choice),
BisGame (<<a, c, sl, sr>>) (<<a, c', sl', sr'>>) -> BisGame sr sr'.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma BisGame_then_Biss2g: forall s s':StratProf, s =sbisg= s' -> (s2g s) =gbis= (s2g s').
Proof.
cofix H.
intros.
replace (s2g s) with (Game_identity (s2g s)).
replace (s2g s') with (Game_identity (s2g s')).
destruct s.
destruct s'.
simpl.
replace u with u0.
apply bisim_gLeaf.
inversion H0; trivial.
inversion H0.
destruct s'.
inversion H0.
simpl.
replace a0 with a.
apply bisim_gNode.
apply H; inversion H0; assumption.
apply H; inversion H0; assumption.
inversion H0. trivial.
apply Game_decomposition.
apply Game_decomposition.
Qed.

Lemma Biss2g_then_Bisgame: forall s s':StratProf, (s2g s) =gbis= (s2g s') -> s =sbisg= s'.
Proof.
cofix H.
intros s s'.
replace (s2g s) with (Game_identity (s2g s)).
replace (s2g s') with (Game_identity (s2g s')).
simpl.
intro H_gBis.
destruct s.
destruct s'.
replace u with u0.
apply BGLeaf.
inversion H_gBis.  trivial.
inversion H_gBis.
destruct s'.
inversion H_gBis.
replace a0 with a.
apply BGNode.
apply H. inversion H_gBis. assumption.
apply H. inversion H_gBis. assumption.
inversion H_gBis. trivial.
apply Game_decomposition.
apply Game_decomposition.
Qed.

Lemma Biss2g_is_Bisgame: forall s s':StratProf, (s2g s) =gbis= (s2g s') <-> s =sbisg= s'.
Proof.
split.
apply Biss2g_then_Bisgame.
apply BisGame_then_Biss2g.
Qed.

        (** **   Utilities, histories, and strategies     *)
Inductive s2u : StratProf -> Agent -> Utility -> Prop :=
| s2uLeaf: forall a f, s2u (<<f>>) a (f a)
| s2uLeft: forall  (a a':Agent) (u:Utility) (sl sr:StratProf),
    s2u sl a u  -> s2u (<<a',l,sl,sr>>) a u  
| s2uRight: forall (a a':Agent) (u:Utility) (sl sr:StratProf),
    s2u sr a u -> s2u (<<a',r,sl,sr>>) a u.

Lemma s2uLeft_rev :  forall  (a a':Agent) (u:Utility) (sl: StratProf) (sr:StratProf),
  s2u (<<a',l,sl,sr>>) a u -> s2u sl a u.
Proof.
intros a a' u sl sr H.
inversion H.
assumption.
Qed.

Lemma s2uRight_rev :  forall  (a a':Agent) (u:Utility) (sl sr: StratProf),
  s2u (<<a',r,sl,sr>>) a u -> s2u sr a u.
Proof.
intros a a' u sl sr H.
inversion H.
assumption.
Qed.

(** - The history of a strategy *)
CoFixpoint s2h (s:StratProf): History:=
match s with
| <<f>> => HNil 
| <<a,l,sl,sr>> => HCons l (s2h sl)
| <<a,r,sl,sr>> => HCons r (s2h sr)
end.

Lemma s2h_and_g: forall (s:StratProf),(s2h s) >is_history_of (s2g s).
Proof.
cofix H.
intros.
replace (s2g s) with (Game_identity (s2g s)).
replace (s2h s) with (History_identity (s2h s)).
destruct s.
simpl.
apply hist_Leaf.
case c.
simpl.
apply  hist_NodeLeft.
apply H.
simpl.
apply hist_NodeRight.
apply H.
apply History_decomposition.
apply Game_decomposition.
Qed.


        (*   --------------------------------------- *)
        (** * Leads to Leaf and Always Leads to Leaf *) 
        (*   --------------------------------------- *)

          (** - Leads to a Leaf *)

Inductive LeadsToLeaf: StratProf -> Prop :=
| LtLLeaf: forall f, LeadsToLeaf (<<f>>)
| LtLLeft: forall (a:Agent)(sl: StratProf) (sr:StratProf),
    LeadsToLeaf sl -> LeadsToLeaf (<<a,l,sl,sr>>)
| LtLRight: forall (a:Agent)(sl: StratProf) (sr:StratProf),
     LeadsToLeaf sr -> LeadsToLeaf (<<a,r,sl,sr>>).

Lemma LtL_revLeft : forall (a: Agent) (sl sr : StratProf), LeadsToLeaf (<<a,l,sl,sr>>) -> LeadsToLeaf(sl).
intros a sl sr ltl.
inversion ltl.
assumption.
Qed.

Lemma LtL_revRight : forall (a: Agent) (sl sr : StratProf), LeadsToLeaf (<<a,r,sl,sr>>) -> LeadsToLeaf(sr).
intros a sl sr ltl.
inversion ltl.
assumption.
Qed.

(*LeadsToLeaf is the contrary of hasInfiniteHistory*)
Lemma LeadsToLeaf_then_not_hasInfiniteHistory: forall s: StratProf,
LeadsToLeaf s -> ~ hasInfiniteHistory s.
Proof.
intros s LtL_s.
induction LtL_s; unfold not; intro infHist; inversion infHist.
apply IHLtL_s. apply H0.
apply IHLtL_s. apply H0.
Qed.

Lemma hasInfiniteHistory_then_not_LeadsToLeaf: forall s: StratProf,
hasInfiniteHistory s -> ~LeadsToLeaf s.
Proof.
unfold not.
intros s inf ltl.
cut (LeadsToLeaf s -> ~ hasInfiniteHistory s).
unfold not.
intro H.
apply H.
apply ltl.
apply inf.
apply LeadsToLeaf_then_not_hasInfiniteHistory.
Qed.
 
Lemma not_LeadsToLeaf_then_hasInfiniteHistory: forall s: StratProf,
~LeadsToLeaf s -> hasInfiniteHistory s.
Proof.
cofix H.
unfold not.
intro s.
case s.
intros u not_LtL_s.
cut False.
intuition.
apply not_LtL_s.
apply LtLLeaf.

intros a c.
case c.
intros s0 s1 not_LtL_s.
apply InfHistLeft.
apply H.
unfold not.
intro LtL_s0.
apply not_LtL_s.
apply LtLLeft. assumption.
intros s0 s1 not_LtL_s.
apply InfHistRight.
apply H.
unfold not.
intro LtL_s0.
apply not_LtL_s.
apply LtLRight. assumption.
Qed.

Require Import Classical.
Lemma not_hasInfiniteHistory_then_LeadsToLeaf: forall s: StratProf,
~hasInfiniteHistory s -> LeadsToLeaf s.
Proof.
intros s notInf.
cut (LeadsToLeaf s \/ ~LeadsToLeaf s).
intros classic.
destruct classic.
assumption.
cut False.
intuition.
apply notInf.
apply not_LeadsToLeaf_then_hasInfiniteHistory.
assumption.
apply classic.
Qed.


(** - Existence and uniqueness of the utility of a strategy, only if LeadsToLeaf *)
Lemma Existence_s2u :  forall (a:Agent) (s:StratProf),
  LeadsToLeaf s -> exists u:Utility, s2u s a u.
Proof.
intros a s.
induction 1.
exists (f a).
apply  s2uLeaf.
elim IHLeadsToLeaf.
intros u Hs2u.
exists u.
apply s2uLeft with (a:=a)(a':=a0)(sl:=sl)(sr:=sr).
assumption.
elim IHLeadsToLeaf.
intros u Hs2u.
exists u.
apply s2uRight with (a:=a)(a':=a0)(sl:=sl)(sr:=sr).
assumption.
Qed.

Lemma Uniqueness_s2u: forall (a:Agent) (u v:Utility) (s:StratProf), s2u s a u -> s2u s a v -> u=v.
Proof.
intros a u v s s2u_u s2u_v.
generalize s2u_u; generalize s2u_v.
induction s2u_u.
intros. inversion s2u_v. reflexivity.
intros. inversion s2u_v. apply IHs2u_u. apply H4. apply H4. apply s2u_u.
intros. inversion s2u_v. apply IHs2u_u. apply H4. apply H4. apply s2u_u.
Qed.

Lemma existence_then_LeadsToLeaf: forall (s: StratProf) (a:Agent),
(exists u, s2u s a u) ->LeadsToLeaf s.
Proof.
intros.
induction H.
induction H.
apply LtLLeaf.
apply LtLLeft. assumption.
apply LtLRight. assumption.
Qed.


	(** Even Leads to leaf*)
Inductive evenLTL: StratProf -> Prop :=
| ELtL_Leaf: forall f, evenLTL (<<f>>)
| ELtL_LeafL: forall f (a: Agent) (s :StratProf), evenLTL (<<a, l,(<<f>>), s>>)
| ELtL_LeafR: forall f (a: Agent) (s :StratProf), evenLTL (<<a, r,s, (<<f>>)>>)
| ELtL_LL: forall (a a':Agent) (sl' sr' sr:StratProf),
    evenLTL sl' -> evenLTL (<<a,l,(<<a',l,sl',sr'>>),sr>>)
| ELtL_LR: forall (a a':Agent) (sl' sr' sr:StratProf),
    evenLTL sr' -> evenLTL (<<a,l,(<<a',r,sl',sr'>>),sr>>)
| ELtL_RL: forall (a a':Agent) (sl' sr' sl:StratProf),
    evenLTL sl' -> evenLTL (<<a,r,sl,(<<a',l,sl',sr'>>)>>)
| ELtL_RR: forall (a a':Agent) (sl' sr' sl:StratProf),
    evenLTL sr' -> evenLTL (<<a,r,sl,(<<a',r,sl',sr'>>)>>)
.
Lemma evenLtL_then_LtL : forall s: StratProf, evenLTL s -> LeadsToLeaf s.
Proof.
intros s even_s.
induction even_s.
apply LtLLeaf.
apply LtLLeft.
apply LtLLeaf.
apply LtLRight.
apply LtLLeaf.
apply LtLLeft.
apply LtLLeft.
apply IHeven_s.
apply LtLLeft.
apply LtLRight.
apply IHeven_s.
apply LtLRight.
apply LtLLeft.
apply IHeven_s.
apply LtLRight.
apply LtLRight.
apply IHeven_s.
Qed.

Lemma even_aux : forall (s : StratProf), evenLTL s -> 
forall (a: Agent) (s': StratProf),  (evenLTL (<<a, l, s, s'>>) /\ evenLTL (<<a,r,s',s>>)).
Proof.
intros s even_s.
induction even_s.
split.
apply ELtL_LeafL.
apply ELtL_LeafR.

intros a0 sr.
split.
apply ELtL_LL. apply ELtL_Leaf.
apply ELtL_RL. apply ELtL_Leaf.
intros.
split.
apply ELtL_LR. apply ELtL_Leaf.
apply ELtL_RR. apply ELtL_Leaf.

intros a0 s'.
cut (evenLTL (<< a', l, sl', sr' >>) /\ evenLTL (<< a', r, sr', sl' >>)).
intros and.
split.
apply ELtL_LL.
destruct and; assumption.
apply ELtL_RL.
destruct and; assumption.
apply IHeven_s.

intros a0 s'.
cut (evenLTL (<< a', r, sl', sr' >>) /\ evenLTL (<< a', l, sr', sl' >>)).
intros and.
split.
apply ELtL_LL.
destruct and; assumption.
apply ELtL_RL.
destruct and; assumption.
cut (evenLTL (<< a', l, sr', sl' >> )/\evenLTL(<< a', r, sl', sr' >>) ).
intuition.
apply IHeven_s.

intros a0 s'.
cut (evenLTL (<< a', l, sl', sr' >>)).
intros and.
split.
apply ELtL_LR.
assumption.
apply ELtL_RR.
assumption.
cut (evenLTL (<< a', l, sl', sr' >> )/\evenLTL(<< a', r, sr', sl' >>) ).
intuition.
apply IHeven_s.

intros a0 s'.
cut (evenLTL (<<a',r,sl',sr'>>) ).
intros and.
split.
apply ELtL_LR.
assumption.
apply ELtL_RR.
assumption.
cut (evenLTL (<< a', l, sr', sl' >> )/\evenLTL(<< a', r, sl', sr' >>) ).
intuition.
apply IHeven_s.
Qed.

Lemma even_left : forall (a : Agent) ( s' s : StratProf), evenLTL s -> evenLTL (<<a, l, s, s'>>).
Proof.
intros a s' s evenLTL_s.
cut (evenLTL (<<a, l, s, s'>>) /\ evenLTL (<<a, r, s', s>>)).
intuition.
apply even_aux.
assumption.
Qed.

Lemma even_right : forall (a : Agent) ( s' s : StratProf), evenLTL s -> evenLTL (<<a, r, s', s>>).
Proof.
intros a s' s evenLTL_s.
cut (evenLTL (<<a, l, s, s'>>) /\ evenLTL (<<a, r, s', s>>)).
intuition.
apply even_aux.
assumption.
Qed.

Lemma LtL_then_evenLtL : forall s: StratProf, LeadsToLeaf s ->evenLTL s.
Proof.
intros s ltl_s.
induction ltl_s.
apply ELtL_Leaf.
apply even_left. assumption.
apply even_right. assumption.
Qed.


        (** - Leads Always to a Leaf **)

CoInductive AlwLeadsToLeaf: StratProf -> Prop :=
| ALtLeaf : forall (f:Utility_fun), AlwLeadsToLeaf (<<f>>)
| ALtL : forall (a:Agent)(c:Choice)(sl sr:StratProf),
    LeadsToLeaf (<<a,c,sl,sr>>) -> AlwLeadsToLeaf sl ->AlwLeadsToLeaf sr -> 
    AlwLeadsToLeaf (<<a,c,sl,sr>>).

Lemma ALtL_then_LtL: forall (s: StratProf), AlwLeadsToLeaf s -> LeadsToLeaf s.
Proof.
intros.
inversion H.
apply LtLLeaf.
assumption.
Qed.

Lemma ALtLLeft: forall a c sl sr,  AlwLeadsToLeaf (<<a,c,sl,sr>>) -> AlwLeadsToLeaf sl.
Proof.
intros.
inversion H.
assumption.
Qed.

Lemma ALtLRight: forall a c sl sr,  AlwLeadsToLeaf (<<a,c,sl,sr>>) -> AlwLeadsToLeaf sr.
Proof.
intros.
inversion H.
assumption.
Qed.


        (*    -----------------  *)
        (** * Convertibilities   *)
        (*    -----------------  *)

(** - An inductive convertibility *)
Inductive IndAgentConv: Agent -> StratProf -> StratProf -> Prop :=
| ConvRefl: forall (a:Agent)(s: StratProf), IndAgentConv a s s
| ConvAgent :  forall (a:Agent)(c c':Choice)(sl sl' sr sr':StratProf),
  (IndAgentConv a sl sl') -> (IndAgentConv a sr sr') -> 
  IndAgentConv a (<<a,c,sl,sr>>) (<<a,c',sl',sr'>>)
| ConvChoice :  forall (a a':Agent) (c: Choice) (sl sl' sr sr':StratProf),
  IndAgentConv a sl sl' -> (IndAgentConv a sr sr') -> 
  IndAgentConv a (<<a',c,sl,sr>>) (<<a',c,sl',sr'>>).

(* Notation *) Notation "sl |-- a --| sr" := (IndAgentConv a sl sr) (at level 70).

(** - Some Lemmas *) 
Lemma IndConvSameGame: forall a s s', s |--a--| s' -> s =sbisg= s'.
Proof.
intros.
elim H.
intros.
apply BisGame_refl.
intros.
apply BGNode; assumption.
intros.
apply BGNode; assumption.
Qed.

Lemma IndConvSym: forall a s s', s|--a--|s' -> s'|--a--|s. 
Proof.
intros a s s' H.
elim H.
apply ConvRefl.
intros.  
apply ConvAgent.  assumption.  assumption.
intros; apply ConvChoice.
assumption. assumption.
Qed.

Lemma IndConvSameHeadAgent: 
forall (a a' a'':Agent)(c c':Choice)(sl sl' sr sr': StratProf),
  (<<a,c,sl,sr>>) |--a''--| (<<a',c',sl',sr'>>) -> a=a'.
Proof.
intros.
inversion H; trivial.
Qed.

Lemma IndConvLeaf: forall a f s, s|--a--|(<<f>>) -> s = <<f>>.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma IndConvProjL: forall (a a' a'':Agent)(c c':Choice)(sl sl' sr sr':StratProf),
  (<<a,c,sl,sr>>)|--a''--|(<<a',c',sl',sr'>>) -> sl |--a''--| sl'.
Proof.
intros.
inversion H.
apply ConvRefl.
assumption.
assumption.
Qed.

Lemma IndConvProjR: forall (a a' a'':Agent)(c c':Choice)(sl sl' sr sr':StratProf),
  (<<a,c,sl,sr>>)|--a''--|(<<a',c',sl',sr'>>) -> sr |--a''--|sr'.
Proof.
intros.
inversion H.
apply ConvRefl.
assumption.
assumption.
Qed.

Lemma IndConvTrans:  forall (a:Agent)(s s': StratProf),
  s|--a--|s' -> forall (s'': StratProf), s'|--a--| s'' -> s|--a--|s''. 
Proof.
induction 1.
trivial.

intros s''.
case s''.
intros.
inversion H1.
intros a' c0 sl'' sr'' Hyp.
replace a' with a.
apply ConvAgent.
apply IHIndAgentConv1.
apply IndConvProjL with (a:=a)(a':=a')(a'':=a)(c:=c')(c':=c0)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IHIndAgentConv2.
apply IndConvProjR with (a:=a)(a':=a')(a'':=a)(c:=c')(c':=c0)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IndConvSameHeadAgent with (a'':=a)(c:=c')(c':=c0)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.

intros s''.
case s''.
intros.
inversion H1.
intros a'' c'' sl'' sr'' Hyp.
replace a'' with a'.
generalize Hyp.
case c.
case c''.
intros.
apply ConvChoice.
apply IHIndAgentConv1.
apply IndConvProjL with (a:=a')(a':=a'')(a'':=a)(c:=l)(c':=l)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IHIndAgentConv2.
apply IndConvProjR with (a:=a')(a':=a'')(a'':=a)(c:=l)(c':=l)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.

intros.
replace a' with a.
apply ConvAgent.
apply IHIndAgentConv1.
apply IndConvProjL with (a:=a')(a':=a'')(a'':=a)(c:=c)(c':=c'')(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IHIndAgentConv2.
apply IndConvProjR with (a:=a')(a':=a'')(a'':=a)(c:=c)(c':=c'')(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
inversion Hyp0; trivial.

case c''.
intros.
replace a' with a.
apply ConvAgent.
apply IHIndAgentConv1.
apply IndConvProjL with (a:=a')(a':=a'')(a'':=a)(c:=r)(c':=l)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IHIndAgentConv2.
apply IndConvProjR with (a:=a')(a':=a'')(a'':=a)(c:=r)(c':=l)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
inversion Hyp0. trivial.

intros.
apply ConvChoice.
apply IHIndAgentConv1.
apply IndConvProjL with (a:=a')(a':=a'')(a'':=a)(c:=r)(c':=r)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IHIndAgentConv2.
apply IndConvProjR with (a:=a')(a':=a'')(a'':=a)(c:=r)(c':=r)(sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
apply IndConvSameHeadAgent with (a'':=a) (c:=c) (c':=c'') (sl:=sl')(sr:=sr')(sl':=sl'')(sr':=sr'').
assumption.
Qed.

Lemma AlwLeadsToLeaf_Preservation: forall (a:Agent)(s s':StratProf),
  AlwLeadsToLeaf s -> s|--a--|s' -> AlwLeadsToLeaf s'.
Proof.
induction 2.
  (* Refl *)
assumption.
  (* Agent *)
apply ALtL.
case c'.
apply LtLLeft.
apply ALtL_then_LtL.
apply IHIndAgentConv1.
inversion H.
apply ALtLLeft with (a:=a)(c:=c)(sl:=sl)(sr:=sr).
assumption.
apply LtLRight.
apply ALtL_then_LtL.
apply IHIndAgentConv2.
inversion H.
apply ALtLRight with (a:=a)(c:=c)(sl:=sl)(sr:=sr).
assumption.
apply IHIndAgentConv1.
apply ALtLLeft with (a:=a)(c:=c)(sl:=sl)(sr:=sr).
assumption.
apply IHIndAgentConv2.
apply ALtLRight with (a:=a)(c:=c)(sl:=sl)(sr:=sr).
assumption.
  (* Choice *)
apply ALtL.
case c.
apply LtLLeft.
apply ALtL_then_LtL.
apply IHIndAgentConv1.
inversion H.
apply ALtLLeft with (a:=a')(c:=c)(sl:=sl)(sr:=sr).
assumption.
apply LtLRight.
apply ALtL_then_LtL.
apply IHIndAgentConv2.
inversion H.
apply ALtLRight with (a:=a')(c:=c)(sl:=sl)(sr:=sr).
assumption.
apply IHIndAgentConv1.
apply ALtLLeft with (a:=a')(c:=c)(sl:=sl)(sr:=sr).
assumption.
apply IHIndAgentConv2.
apply ALtLRight with (a:=a')(c:=c)(sl:=sl)(sr:=sr).
assumption.
Qed.


(** - A coinductive convertibility *)
CoInductive CoIndAgentConv: Agent -> StratProf -> StratProf -> Prop :=
| ConvLeafCo: forall (a:Agent)(f:Utility_fun), CoIndAgentConv a (<<f>>) (<<f>>)
| ConvAgentCo :  forall (a:Agent)(c c':Choice)(sl sl' sr sr':StratProf),
  (CoIndAgentConv a sl sl') -> (CoIndAgentConv a sr sr') -> 
  CoIndAgentConv a (<<a,c,sl,sr>>) (<<a,c',sl',sr'>>)
| ConvChoiceCo :  forall (a a':Agent) (c: Choice) (sl sl' sr sr':StratProf),
  CoIndAgentConv a sl sl' -> (CoIndAgentConv a sr sr') -> 
  CoIndAgentConv a (<<a',c,sl,sr>>) (<<a',c,sl',sr'>>).

(* Notation *) Notation "sl <<-- a -->> sr" := ( CoIndAgentConv a sl sr) (at level 70).

Lemma CoIndConvRefl: forall a s, s <<--a-->> s.
Proof.
cofix H.
intros.
case s.
apply ConvLeafCo.
intros.
apply ConvChoiceCo.
apply H.
apply H.
Qed.

Lemma IndConv_then_CoIndConv: forall a s s', s |--a--| s' -> s <<--a-->> s'.
Proof.
induction 1; [apply  CoIndConvRefl | apply ConvAgentCo | apply ConvChoiceCo]; assumption.
Qed.

Lemma CoIndConvSameGame': forall a s s', s <<--a-->> s' -> s =sbisg= s'.
Proof.
cofix H.
intros.
destruct s.
destruct s'.
inversion H0.
apply BGLeaf.
inversion H0.
destruct s'.
inversion H0.
replace a0 with a1.
apply  BGNode.
apply H with (a:=a).
inversion H0;  assumption.
apply H with (a:=a).
inversion H0;  assumption.
inversion H0; apply refl_equal.
Qed.

Lemma CoIndConvSameGame: forall a s s', s <<--a-->> s' -> (s2g s) =gbis= (s2g s').
Proof.
intros.
apply BisGame_then_Biss2g.
apply CoIndConvSameGame' with (a:=a).
assumption.
Qed.

(*Equivalence*)
CoInductive CoEq :  StratProf -> StratProf -> Prop :=
|CoEq_Same: forall (s : StratProf) , CoEq s s
|CoEq_Left : forall (a: Agent) (sl sl' sr sr': StratProf), CoEq sl sl' -> CoEq (<<a, l, sl, sr>>) (<<a, l, sl', sr'>>)
|CoEq_Right : forall (a: Agent) (sl sl' sr sr': StratProf), CoEq sr sr' -> CoEq (<<a, r, sl, sr>>) (<<a, r, sl', sr'>>)
.

Lemma Eq_RevLeft : forall (a: Agent) (sl sl' sr sr' :StratProf) , 
CoEq (<<a, l, sl, sr>>) (<<a, l, sl', sr'>>) -> CoEq sl sl'.
Proof.
intros a sl sl' sr sr' H.
inversion H.
apply CoEq_Same.
assumption.
Qed.

Lemma Eq_RevRight : forall (a: Agent) (sl sl' sr sr' :StratProf) , 
CoEq (<<a, r, sl, sr>>) (<<a, r, sl', sr'>>) -> CoEq sr sr'.
Proof.
intros a sl sl' sr sr' H.
inversion H.
apply CoEq_Same.
assumption.
Qed.

Lemma Eq_SameChoice : forall (a: Agent) (c c' : Choice) (sl sl' sr sr': StratProf),
CoEq (<<a, c, sl, sr>>) (<<a, c', sl', sr'>>) -> c= c'.
Proof.
intros a c c' sl sl' sr sr' H.
inversion H.
trivial. trivial. trivial.
Qed.

   (*    ----------- *)
   (* Equilibria  *)
   (*    ----------- *)

    (** -  Nash equilibria for infinite games *)
Definition NashEq (s: StratProf): Prop := 
  forall a s' u u', s'|--a--|s ->  (s2u s' a u') -> (s2u s a u) -> 
    (u' =< u).

Definition betterFor (a: Agent) (s s' : StratProf): Prop :=
forall u u',
 (s2u s' a u') ->  (s2u s a u) -> 
(u' =< u).


    (** - SubGame Perfect Equilibrium (SGPE) for infinite games *)
CoInductive SGPE: StratProf -> Prop :=
| SGPE_leaf: forall f:Utility_fun, SGPE (<<f>>)
| SGPE_left: forall (a:Agent)(u v: Utility) (sl sr: StratProf), 
    AlwLeadsToLeaf (<<a,l,sl,sr>>) -> 
    SGPE sl -> SGPE sr -> 
    s2u sl a u -> s2u sr a v -> (v =< u) ->
    SGPE (<<a,l,sl,sr>>)
| SGPE_right: forall (a:Agent) (u v:Utility) (sl sr: StratProf), 
    AlwLeadsToLeaf (<<a,r,sl,sr>>) -> 
    SGPE sl -> SGPE sr -> 
    s2u sl a u -> s2u sr a v -> (u =< v) -> 
    SGPE (<<a,r,sl,sr>>). 

Lemma SGPE_then_AlwLeadsToLeaf: forall s:StratProf, SGPE s -> AlwLeadsToLeaf s.
Proof.
intros.
inversion H.
apply ALtLeaf.
assumption.
assumption.
Qed.

Lemma SGPE_rev_Left : forall (a:Agent) (c:Choice) (sl sr: StratProf),
     SGPE (<<a,c,sl,sr>>) ->  SGPE sl.
Proof.
intros; case c; inversion H; assumption.
Qed.

Lemma SGPE_rev_Right: forall (a:Agent) (c:Choice) (sl sr: StratProf),
     SGPE (<<a,c,sl,sr>>) ->  SGPE sr.
Proof.
intros; case c; inversion H; assumption.
Qed.

Lemma SGPE_then_SubStrat_SGPE:  forall (a:Agent) (c:Choice) (sl sr: StratProf),
     SGPE (<<a,c,sl,sr>>) ->  SGPE sl /\ SGPE sr.
Proof.
intros. split.
apply SGPE_rev_Left with (a:=a)(c:=c)(sr:=sr). assumption.
apply SGPE_rev_Right with (a:=a)(c:=c)(sl:=sl). assumption.
Qed.

Lemma SGPE_then_LtL : forall (s : StratProf), SGPE s -> LeadsToLeaf s.
Proof.
intros s SGPE_s.
apply ALtL_then_LtL.
apply SGPE_then_AlwLeadsToLeaf.
assumption.
Qed. 

Lemma SGPE_implies_BetterFor: forall (s s': StratProf) (a: Agent), s |-- a --| s' -> SGPE s -> betterFor a s s'.
Proof.
intros s s' a conv.
induction conv.
intro SGPE_s.
unfold betterFor.
intros u u'  s2u_s'  s2u_s.
replace u' with u.

apply (preord_refl Utility preference preference_is_preorder). 
eapply Uniqueness_s2u.
apply s2u_s.
apply s2u_s'.


intros SGPE_s.

cut (LeadsToLeaf sl). cut (LeadsToLeaf sl'). cut (LeadsToLeaf sr). cut (LeadsToLeaf sr').
intros ltl_sr' ltl_sr ltl_sl' ltl_sl.
intros u u' s2u_s'  s2u_s.
unfold betterFor.
cut (exists ul, s2u sl a ul).
cut (exists ul', s2u sl' a ul').
cut (exists ur, s2u sr a ur).
cut (exists ur', s2u sr'  a ur').
intros s2u_sr' s2u_sr s2u_sl' s2u_sl.
elim s2u_sr'. elim s2u_sr. elim s2u_sl'. elim s2u_sl.
intros ul s2ul ul' s2ul' ur s2ur ur' s2ur'.

cut (ul' =< ul). cut (ur' =< ur).
intros ur'_inf_ur ul'_inf_ur.

inversion SGPE_s.
cut ( ul = u0). cut (ur = v).
intros ur_equal_v ul_equal_u0.
cut (u=ul).
intros u_equal_ul.
rewrite u_equal_ul.
inversion s2u_s'.
cut (u' = ul').
intros u'_equal_ul'.
rewrite u'_equal_ul'.
exact ul'_inf_ur.
eapply Uniqueness_s2u.
apply H15.
apply s2ul'.

cut (ur' = u').
intro ur'_equal_u'.
rewrite<-ur'_equal_u'.
cut (ur =< ul).
intro ur_inf_ul.
inversion preference_is_preorder.
apply preord_trans with ur.
apply ur'_inf_ur.
apply ur_inf_ul.
rewrite ur_equal_v. rewrite ul_equal_u0.
exact H8.
eapply Uniqueness_s2u.
apply s2ur'.
apply H15.
eapply Uniqueness_s2u.


eapply s2uLeft_rev.
rewrite H0.
apply s2u_s.
apply s2ul.
eapply Uniqueness_s2u.
apply s2ur.
apply H7.
eapply Uniqueness_s2u.
apply s2ul.
apply H6.

(* Si c = r *)
inversion SGPE_s.
(*Si c = l, c'est pas possible*)
cut False. 
intro false.
intuition.
cut (l=r).
intro l_equal_r.
inversion l_equal_r.
rewrite H10.
rewrite H0.
reflexivity.

cut (u=ur).
intros u_equal_ul.
rewrite u_equal_ul.
inversion s2u_s'.
cut (u' = ul').
intros u'_equal_ul'.
rewrite u'_equal_ul'.
inversion preference_is_preorder.
apply preord_trans with ul.
exact ul'_inf_ur.
cut (ul = u0). cut (ur = v).
intros ur_equal_v ul_equal_u0.
rewrite ur_equal_v. rewrite ul_equal_u0.
exact H8.
eapply Uniqueness_s2u.
apply s2ur.
apply H7.
eapply Uniqueness_s2u.
apply s2ul.
apply H6.

eapply Uniqueness_s2u.
apply H25.
apply s2ul'.
cut (u'= ur').
intro u'_equal_ur'.
rewrite u'_equal_ur'.
apply ur'_inf_ur.
eapply Uniqueness_s2u.
apply H25.
apply s2ur'.
eapply Uniqueness_s2u.
eapply s2uRight_rev.
rewrite H10.
apply s2u_s.
apply s2ur.


cut (betterFor a sr sr').
unfold betterFor.
intros unfolded_betterFor.
apply unfolded_betterFor.

apply s2ur'.
apply s2ur.
apply IHconv2.
eapply SGPE_rev_Right with (a:=a)(c:=c)(sr:=sr).
apply SGPE_s.


cut (betterFor a sl sl').
unfold betterFor.
intros unfolded_betterFor.
apply unfolded_betterFor.

apply s2ul'.
apply s2ul.
apply IHconv1.
eapply SGPE_rev_Left with (a:=a)(c:=c)(sl:=sl).
apply SGPE_s.

apply Existence_s2u.
apply ltl_sr'.
apply Existence_s2u.
apply ltl_sr.
apply Existence_s2u.
apply ltl_sl'.
apply Existence_s2u.
apply ltl_sl.
apply ALtL_then_LtL.
eapply AlwLeadsToLeaf_Preservation.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Right.
apply SGPE_s.
apply conv2.
apply ALtL_then_LtL.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Right.
apply SGPE_s.
apply ALtL_then_LtL.
eapply AlwLeadsToLeaf_Preservation.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Left.
apply SGPE_s.
apply conv1.
apply ALtL_then_LtL.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Left.
apply SGPE_s.

intros SGPE_s.
cut (LeadsToLeaf sl). cut (LeadsToLeaf sl'). cut (LeadsToLeaf sr). cut (LeadsToLeaf sr').
intros ltl_sr' ltl_sr ltl_sl' ltl_sl.
unfold betterFor.
intros u u'  s2u_s' s2u_s.

cut (exists ul, s2u sl a ul).
cut (exists ul', s2u sl' a ul').
cut (exists ur, s2u sr a ur).
cut (exists ur', s2u sr'  a ur').
intros s2u_sr' s2u_sr s2u_sl' s2u_sl.
elim s2u_sr'. elim s2u_sr. elim s2u_sl'. elim s2u_sl.
intros ul s2ul ul' s2ul' ur s2ur ur' s2ur'.

induction c.
cut (u'= ul'). cut (u=ul).
intros u_equal_ul u'_equal_ul'.
rewrite u_equal_ul. rewrite u'_equal_ul'.
cut (betterFor a sl sl').
unfold betterFor.
intros better_sl_sl'.
apply better_sl_sl'.
apply s2ul'.
apply s2ul.
apply IHconv1.
eapply SGPE_rev_Left.
apply SGPE_s.
eapply Uniqueness_s2u.
eapply s2uLeft_rev.
apply s2u_s.
apply s2ul.
eapply Uniqueness_s2u.
eapply s2uLeft_rev.
apply s2u_s'.
apply s2ul'.

cut (u'= ur'). cut (u=ur).
intros u_equal_ur u'_equal_ur'.
rewrite u_equal_ur. rewrite u'_equal_ur'.
cut (betterFor a sr sr').
unfold betterFor.
intros better_sr_sr'.
apply better_sr_sr'.
apply s2ur'.
apply s2ur.
apply IHconv2.
eapply SGPE_rev_Right.
apply SGPE_s.
eapply Uniqueness_s2u.
eapply s2uRight_rev.
apply s2u_s.
apply s2ur.
eapply Uniqueness_s2u.
eapply s2uRight_rev.
apply s2u_s'.
apply s2ur'.

apply Existence_s2u.
apply ltl_sr'.
apply Existence_s2u.
apply ltl_sr.
apply Existence_s2u.
apply ltl_sl'.
apply Existence_s2u.
apply ltl_sl.
apply ALtL_then_LtL.
eapply AlwLeadsToLeaf_Preservation.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Right.
apply SGPE_s.
apply conv2.
apply ALtL_then_LtL.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Right.
apply SGPE_s.
apply ALtL_then_LtL.
eapply AlwLeadsToLeaf_Preservation.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Left.
apply SGPE_s.
apply conv1.
apply ALtL_then_LtL.
apply SGPE_then_AlwLeadsToLeaf.
eapply SGPE_rev_Left.
apply SGPE_s.
Qed.

Theorem SGPE_Implies_NashEq: forall (s: StratProf), SGPE s -> NashEq s.
Proof.
intros s SGPE_s.
unfold NashEq.
intros a s' u u' conv s2u_s' s2u_s.
cut (betterFor a s s').
unfold betterFor.
intro betterFor_s_s'.
apply betterFor_s_s'.
assumption. assumption. 
apply SGPE_implies_BetterFor.
apply IndConvSym.
assumption. assumption.
Qed.

        (*  ----------------- *)
        (** *   Escalation    *)
        (*  ----------------- *)

Definition has_an_escalation_sequence (g_seq:nat -> Game): Prop := forall n:nat, 
exists s,  exists s', exists a, 
  (s2g (<<a,l,s,s'>>) =gbis= g_seq n /\ SGPE (<<a,l,s,s'>>) \/
  s2g (<<a,r,s',s>>) =gbis= g_seq n /\ SGPE (<<a,r,s',s>>)) /\
  s2g s =gbis= g_seq (n+1).


Definition has_an_escalation (g:Game) : Prop :=
    exists g_seq, (has_an_escalation_sequence g_seq) /\ (g_seq 0 = g).
  
End InfiniteExtensiveGames.
