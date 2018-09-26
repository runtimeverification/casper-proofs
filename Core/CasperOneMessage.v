From mathcomp
Require Import all_ssreflect.

From Hammer
Require Import Reconstr.

Section CasperOneMessage.

Variable Validator : finType.
Variable Hash : finType.

Variable quorum_1 : {set {set Validator}}.
Variable quorum_2 : {set {set Validator}}.

Hypothesis quorums_intersection :
  forall q1 q2, q1 \in quorum_1 -> q2 \in quorum_1 ->
  exists q3, q3 \in quorum_2 /\ q3 \subset q1 /\ q3 \subset q2.

Lemma quorums_property :
 forall q1 q2, q1 \in quorum_1 -> q2 \in quorum_1 ->
 exists q3, q3 \in quorum_2 /\ forall n, n \in q3 -> n \in q1 /\ n \in q2.
Proof.
move => q1 q2 Hq1 Hq2.
have [q3 [Hq3 [Hq13 Hq23]]] := (quorums_intersection _ _ Hq1 Hq2).
exists q3.
split => //.
move => n Hn.
split.
- by apply/(subsetP Hq13).
- by apply/(subsetP Hq23).
Qed.

(* vote_msg node hash view view_src *)
Record State :=
 { vote_msg : Validator -> Hash -> nat -> nat -> bool }.

Variable hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

Variable genesis : Hash.

Hypothesis hash_at_most_one_parent_1 :
  forall h1 h2, h1 <~ h2 -> h1 <> h2.

Hypothesis hash_at_most_one_parent_2 :
  forall h1 h2 h3, h2 <~ h1 -> h3 <~ h1 -> h2 = h3.

Definition hash_ancestor h1 h2 :=
 connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

Definition hash_ancestor_base : forall h1 h2,
  h1 <~ h2 -> h1 <~* h2.
Proof.
by apply/connect1.
Qed.

Definition hash_ancestor_step : forall h1 h2 h3,
 h1 <~ h2 -> h2 <~* h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3.
move/connect1.
by apply/connect_trans.
Qed.

Lemma hash_ancestor_intro' :
  forall h1 h2 h3, h1 <~* h2 -> h2 <~ h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3 H1 H2.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

Lemma hash_ancestor_concat :
  forall h1 h2 h3, h2 <~* h3 -> h1 <~* h2 -> h1 <~* h3.
Proof.
move => h1 h2 h3 H2 H1.
by apply: connect_trans; eauto.
Qed.

Lemma hash_ancestor_other:
  forall h1 h2 p, h1 <~* h2 -> p </~* h2 -> p </~* h1.
Proof.
move => h1 h2 p H1 H2.
move => Hp.
case: H2.
move: Hp H1.
by apply/connect_trans.
Qed.

(* steps to ancestor is at least n *)
Inductive nth_ancestor : nat -> Hash -> Hash -> Prop :=
| nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
| nth_ancestor_nth : forall n h1 h2 h3,
    nth_ancestor n h1 h2 -> h2 <~ h3 ->
    nth_ancestor n.+1 h1 h3.

Definition justified_link s q parent pre new now :=
  q \in quorum_1 /\
  (forall n, n \in q -> vote_msg s n new now pre) /\
  nth_ancestor (now - pre) parent new /\
  now > pre.

Lemma ancestor_means :
  forall n parent new,
  nth_ancestor n parent new -> n > 0 -> parent <~* new.
Proof.
elim => //=.
move => n IH parent new Hn.
inversion Hn; subst.
case Hn0: (n == 0).
  move/eqP: Hn0 H0 -> => Hnt Hlt.
  inversion Hnt; subst.
  by apply/connect1.
move/negP/negP: Hn0 => Hn0 Hltn.
have Hnn: 0 < n.
  apply: neq0_lt0n.
  by apply/negP/negP.
move: (IH _ _ H0 Hnn) => Hp.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

Lemma justified_means_ancestor :
  forall s q parent pre new now,
  justified_link s q parent pre new now -> parent <~* new.
Proof.
move => s q parent pre new now.
case => [Hn [Ha [Hnn Hw]]] {Ha}.
move: now pre parent new Hw Hnn.
elim => //=.
move => n IH pre parent new Hlt Ha.
inversion Ha; subst; first by apply/connect0.
have Hn0: n0 = n - pre.
  rewrite subSn // in H.
  by apply/succn_inj.
rewrite Hn0 in H0.
case H'n0: (n0 == 0).
  move/eqP: H'n0 => H'n0.
  rewrite H'n0 in Hn0.
  rewrite -Hn0 in H0.
  inversion H0 .
  exact/connect1.
move/negP/negP: H'n0 => H'n0.
have Hp: pre < n.
  rewrite Hn0 in H'n0.
  rewrite -subn_gt0.
  case Hnn: (n - pre); last by apply ltn0Sn.
  rewrite Hnn in Hn0.
  by move/eqP: H'n0.
have IH' := IH _ _ _ Hp H0.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

Inductive justified : State -> Hash -> nat -> Prop :=
| orig : forall s, justified s genesis 0
| follow : forall s parent pre q new now,
    justified s parent pre ->
    justified_link s q parent pre new now ->
    justified s new now.

Definition finalized s q h v child :=
 h <~ child /\ justified s h v /\ justified_link s q h v child v.+1.

Definition fork s :=
  exists h1 h2 q1 q2 v1 v2 c1 c2,
    finalized s q1 h1 v1 c1 /\
    finalized s q2 h2 v2 c2 /\
     h2 </~* h1 /\ h1 </~* h2 /\ h1 <> h2.

Definition slashed_dbl_vote s n :=
 exists h1 h2, h1 <> h2 /\ exists v s1 s2, vote_msg s n h1 v s1 /\ vote_msg s n h2 v s2.

Definition slashed_surround s n :=
  exists h1 h2 v1 v2 s1 s2,
    vote_msg s n h1 v1 s1 /\
     vote_msg s n h2 v2 s2 /\
     v1 > v2 /\ s2 > s1.

Definition slashed s n : Prop :=
 slashed_dbl_vote s n \/ slashed_surround s n.

Definition one_third_slashed s :=
 exists q, q \in quorum_2 /\ forall n, n \in q -> slashed s n.

Lemma l0 : forall s q1 h2 v2 h1 v1,
 justified_link s q1 h2 v2 h1 v1 ->
 v1 > v2.
Proof.
case => vm0 s q1 h2 v2 h1 v1.
Reconstr.scrush.
Qed.

Lemma l02 : forall s q1 q2 h2 v2 h1 v3 h3 c3,
    justified_link s q1 h2 v2 h1 v3.+1 ->
    finalized s q2 h3 v3 c3 ->
    h3 </~* h1 -> v2 < v3 ->
    exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_dbl_vote s n.
Proof.
move => s q1 q2 h2 v2 h1 v3 h3 c3 Hj Hf Hh Hv.
have Hn1: forall n, n \in q1 -> vote_msg s n h1 v3.+1 v2.
  by Reconstr.htrivial (@Hj)
		Reconstr.Empty
		(@justified_link).
have Hn2: forall n, n \in q2 -> vote_msg s n c3 v3.+1 v3.
  by Reconstr.htrivial (@Hf)
		Reconstr.Empty
		(@finalized, @justified_link).
have Hq1: q1 \in quorum_1 by Reconstr.scrush.
have Hq2: q2 \in quorum_1.
  by Reconstr.htrivial (@Hf)
		Reconstr.Empty
		(@finalized, @justified_link).
have He: exists q, q \in quorum_2 /\ forall n, n \in q -> n \in q1 /\ n \in q2.
  by Reconstr.htrivial (@Hq1, @Hq2)
		(@quorums_property)
		Reconstr.Empty.
have He': exists q, q \in quorum_2 /\ forall n, n \in q -> vote_msg s n h1 v3.+1 v2 /\ vote_msg s n c3 v3.+1 v3.
  move: He => [q [Hq Hn]].
  exists q.
  split => //.
  move => n.
  move/Hn => [Hq'1 Hq'2].
  split.
  - by apply Hn1.
  - by apply Hn2.
have Hne: h1 <> c3.
  by Reconstr.htrivial (@Hf, @Hh)
		(@hash_ancestor_base)
		(@finalized); auto.
have Hnen: h1 <> c3 /\ (exists q, q \in quorum_2 /\ forall n, n \in q -> vote_msg s n h1 v3.+1 v2 /\ vote_msg s n c3 v3.+1 v3) by auto.
clear Hn1 Hn2 Hq1 Hq2 He He' Hne.
by Reconstr.hobvious (@Hnen)
		Reconstr.Empty
		(@Coq.Init.Datatypes.is_true, @slashed_dbl_vote).
Qed.

Lemma l01 : forall s q1 q2 h2 v2 h1 h3 v3 c3,
  justified_link s q1 h2 v2 h1 v3.+1 ->
  finalized s q2 h3 v3 c3 ->
  h3 </~* h1 -> v2 < v3 ->
  one_third_slashed s.
Proof.
move => s q1 q2 h2 v2 h1 h3 v3 c3 Hl Hf Hh Hv.
have Hq: exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_dbl_vote s n.
  by Reconstr.hobvious (@Hf, @Hh, @Hv, @Hl)
		(@l02)
		Reconstr.Empty.
by Reconstr.hobvious (@Hq)
		Reconstr.Empty
		(@slashed, @one_third_slashed).
Qed.

Lemma l04 : forall s q1 q2 h2 v2 h1 v1 v3 h3 c3,
 justified_link s q1 h2 v2 h1 v1 ->
 finalized s q2 h3 v3 c3 ->
 v3.+1 < v1 ->
 h3 </~* h1 ->
 v2 < v3 ->
 exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_surround s n.
Proof.
move => s q1 q2 h2 v2 h1 v1 v3 h3 c3 Hj Hf Hv Hh Hv'.
have Hq1: q1 \in quorum_1 by Reconstr.scrush.
have Hq2: q2 \in quorum_1.
  by Reconstr.htrivial (@Hf)
		Reconstr.Empty
		(@finalized, @justified_link).
have H'q1: forall n, n \in q1 -> vote_msg s n h1 v1 v2
  by Reconstr.htrivial (@Hj)
		Reconstr.Empty
		(@justified_link).
have H'q2: forall n, n \in q2 -> vote_msg s n c3 v3.+1 v3
  by Reconstr.htrivial (@Hf)
		Reconstr.Empty
		(@finalized, @justified_link).
have Hq: exists q, q \in quorum_2 /\ forall n, n \in q -> n \in q1 /\ n \in q2
  by Reconstr.htrivial (@Hq1, @Hq2)
		(@quorums_property)
		Reconstr.Empty.
have Hq': exists q, q \in quorum_2 /\ forall n, n \in q -> vote_msg s n h1 v1 v2 /\ vote_msg s n c3 v3.+1 v3.
  by Reconstr.ryelles6 Reconstr.Empty (@Coq.Init.Datatypes.is_true).
have Hn: forall n, (vote_msg s n h1 v1 v2 /\ vote_msg s n c3 v3.+1 v3) -> slashed_surround s n.
  move => n [Hvm Hvm'].
  by exists h1, c3, v1, v3.+1, v2, v3.
by Reconstr.ryelles6 Reconstr.Empty (@Coq.Init.Datatypes.is_true).
Qed.

Lemma l03 : forall s q1 q2 h2 v2 h1 h3 v1 v3 c3,
  justified_link s q1 h2 v2 h1 v1 ->
  finalized s q2 h3 v3 c3 ->
  v1 > v3.+1 ->
  h3 </~* h1 ->
  v2 < v3 ->
  one_third_slashed s.
Proof.
move => s q1 q2 h2 v2 h1 h3 v1 v3 c3 Hj Hf Hlt Ha Hlt'.
have Hq: exists q, q \in quorum_2 /\ forall n, n \in q -> slashed_surround s n.
  by Reconstr.hobvious (@Hf, @Hlt, @Ha, @Hlt', @Hj)
		(@l04)
		Reconstr.Empty.
by Reconstr.hobvious (@Hq)
		Reconstr.Empty
		(@slashed, @one_third_slashed).
Qed.

Lemma l00 : forall s q1 q2 h2 v2 h1 h3 v1 v3 c3,
  justified_link s q1 h2 v2 h1 v1 ->
  finalized s q2 h3 v3 c3 ->
  v1 > v3 ->
  h3 </~* h1 ->
  v2 < v3 ->
  one_third_slashed s.
Proof.
move => s q1 q2 h2 v2 h1 h3 v1 v3 c3 Hj Hf Hv Hh Hv'.
case Hn: (v1 == v3.+1).
  move/eqP: Hn => Hn.
  by Reconstr.hobvious (@Hf, @Hh, @Hv', @Hn, @Hj)
		(@l01)
		(@hash_ancestor).
move/negP/negP/eqP: Hn => Hn.
have Hgt: v3.+1 < v1.
  apply/ltP.
  move/ltP: Hv => Hv.
  by intuition.
by Reconstr.hobvious (@Hf, @Hh, @Hv', @Hgt, @Hj)
		(@l03)
		(@hash_ancestor).
Qed.

Lemma l5sub :
  forall s h1 v1 new now pre pre1,
  (forall n q2, q2 \in quorum_2 -> n \in q2 ->
   vote_msg s n new now pre /\ vote_msg s n h1 v1 pre1) ->
  now = v1 ->
  h1 <> new ->
  forall n q2, q2 \in quorum_2 -> n \in q2 ->
  slashed_dbl_vote s n.
Proof.
by Reconstr.hobvious Reconstr.Empty
		Reconstr.Empty
		(@slashed_dbl_vote).
Qed.

Lemma l5'' : forall s q q1 parent1 pre1 h1 v1 parent pre new now,
  justified_link s q parent pre new now ->
  justified_link s q1 parent1 pre1 h1 v1 ->
  ~ one_third_slashed s ->
  now = v1 ->
  h1 = new.
Proof.
move => s q q1 parent1 pre1 h1 v1 parent pre new now Hj Hj1 Ho Hnv.
have Hq: q \in quorum_1 by Reconstr.scrush.
have Hq1: q1 \in quorum_1 by Reconstr.scrush.  
have [q2 Hq2]: exists q2, q2 \in quorum_2 /\ forall n, n \in q2 -> n \in q /\ n \in q1 by Reconstr.reasy (@quorums_property) Reconstr.Empty.
have Hn: forall n, n \in q2 -> vote_msg s n new now pre /\ vote_msg s n h1 v1 pre1 by Reconstr.scrush.
case H1n: (h1 == new); first by move/eqP: H1n.
move/eqP: H1n => H1n.
have Hd: forall n, n \in q2 -> slashed_dbl_vote s n by Reconstr.rcrush Reconstr.Empty (@Coq.Init.Datatypes.is_true, @slashed_dbl_vote).
by have Hs: one_third_slashed s by Reconstr.rcrush Reconstr.Empty (@slashed, @vote_msg, @one_third_slashed).
Qed.

Lemma l5' :
  forall s h1 v1 h2 v2,
  justified s h2 v2 ->
  justified s h1 v1 ->
  ~ one_third_slashed s ->
  h1 <> h2 ->
  v2 <> v1.
Proof.
move => s h1 v1 h2 v2 Hj1 Hj2 Hs Hneq.
inversion Hj1.
- inversion Hj2; first by rewrite -H3 -H0 in Hneq.
  by Reconstr.scrush.
- inversion Hj2; first by Reconstr.scrush.
  by Reconstr.rcrush (@l5'') Reconstr.Empty.
Qed.

Lemma l5 : forall s q2 h2 v2 xa parent pre,
  finalized s q2 h2 v2 xa ->
  ~ one_third_slashed s ->
  justified s parent pre ->
  parent <> h2 ->
  v2 <> pre.
Proof.
by Reconstr.hcrush Reconstr.Empty
		(@l5')
		(@finalized).
Qed.

Lemma non_equal_case_ind : forall s h1 v1 q2 h2 v2 xa,
  justified s h1 v1 ->
  finalized s q2 h2 v2 xa ->
  h2 </~* h1 ->
  h1 <> h2 ->
  v1 > v2 ->
  one_third_slashed s.
Proof.
move => s h1 v1 q2 h2 v2 xa.
move => Hj Hf Hh Hn Hv.
elim: v1 Hj Hv Hf => //.
move => n IH Hj Hv Hf.
have Hs: one_third_slashed s \/ ~ one_third_slashed s by admit.
case: Hs => Hs //.
Admitted.

Lemma non_equal_case : forall s q1 q2 h1 v1 x h2 v2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v2 xa ->
  h2 </~* h1 ->
  h1 <> h2 ->
  v1 > v2 ->
  one_third_slashed s.
Proof.
by Reconstr.hexhaustive 0 Reconstr.Empty
		(@non_equal_case_ind)
		(@Coq.Init.Datatypes.is_true, @finalized).
Qed.

Lemma equal_case : forall s q1 h1 v1 x q2 h2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v1 xa ->
  h1 <> h2 ->
  one_third_slashed s.
Proof.
move => s q1 h1 v1 x q2 h2 xa Hf Hf' Hh.
have Hq1: q1 \in quorum_1 by Reconstr.scrush.
have Hq2: q2 \in quorum_1 by Reconstr.scrush.
have Hn: forall n, n \in q1 -> vote_msg s n x v1.+1 v1 by Reconstr.scrush.
have Hn': forall n, n \in q2 -> vote_msg s n xa v1.+1 v1 by Reconstr.scrush.
have [q Hq]: exists q, q \in quorum_2 /\ forall n, n \in q -> n \in q1 /\ n \in q2
  by Reconstr.rsimple (@quorums_property) Reconstr.Empty.
have Hq': forall n, n \in q -> vote_msg s n x v1.+1 v1 /\ vote_msg s n xa v1.+1 v1 by Reconstr.scrush.
have Hx: x <> xa.
  move => Hx.
  rewrite Hx in Hf.
  move: Hf => [Hf1 [Hf2 Hf3]].
  move: Hf' => [Hf'1 [Hf'2 Hf'3]].
  by have Hp := hash_at_most_one_parent_2 _ _ _ Hf1 Hf'1.
have Hnn: forall n, vote_msg s n x v1.+1 v1 -> vote_msg s n xa v1.+1 v1 -> slashed_dbl_vote s n.
  move => n Hv1 Hv2.
  rewrite /slashed_dbl_vote.
  exists x,xa.
  split => //.
  by exists v1.+1, v1,v1.
by Reconstr.ryelles6 (@l5) (@finalized).
Qed.

Lemma safety' : forall s q1 h1 v1 x q2 h2 v2 xa,
  finalized s q1 h1 v1 x ->
  finalized s q2 h2 v2 xa ->
  h2 </~* h1 ->
  h1 </~* h2 ->
  h1 <> h2 ->
  one_third_slashed s.
Proof.
move => s q1 h1 v1 x q2 h2 v2 xa Hf Hf' Hh Hh' Hn.
case Hv: (v1 == v2).
  move/eqP: Hv => Hv.
  subst.
  move: Hf Hf' Hn.
  exact: equal_case.
move/eqP: Hv => Hv.
case H1: (v1 > v2).
  move: Hh Hn H1.
  by apply: non_equal_case; eauto.
have Hgt: v2 > v1.
  apply/ltP.
  move/ltP: H1.
  move => Hnn.
  by intuition.
move: Hgt.
by apply: non_equal_case; eauto.
Qed.

Lemma safety : forall s, fork s -> one_third_slashed s.
Proof.
by Reconstr.hobvious Reconstr.Empty
		(@safety')
		(@fork).
Qed.

End CasperOneMessage.
