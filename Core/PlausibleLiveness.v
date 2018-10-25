From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Liveness.

Variable Validator : finType.
Variable Hash : finType.

(* "2/3", quorums sufficient to "justify" a link *)
Variable quorum_1 : {set {set Validator}}.
(* "1/3" we will assume each of these sets contains at least one good node *)
Variable quorum_2 : {set {set Validator}}.

(* The essential property behind 2/3+1/3 - any two sets from quoroum_1
   have as common members the entire contents of some quorum_2 set,
   so any two decisions each with quorum_1-set have overlapping support
   of at least some quorum_2-set, and then of one good node *)
Hypothesis quorums_intersection :
  forall q1 q2, q1 \in quorum_1 -> q2 \in quorum_1 ->
  exists q3, q3 \in quorum_2 /\ q3 \subset q1 /\ q3 \subset q2.

Hypothesis quorum_2_nonempty:
  forall q, q \in quorum_2 -> exists v, v \in q.

Hypothesis quorum_1_nonempty:
  forall q, q \in quorum_1 -> exists v, v \in q.

(* Each vote names source and target nodes by giving hash and height,
   and is signed by a particular validator *)
Definition Vote := (Validator * Hash * Hash * nat * nat)%type.
(* A state includes a finite set of Votes cast in the current epoch *)
Definition State := {fset Vote}.

Definition vote_target_height (v:Vote) : nat :=
  match v with
    (_,_,_,_,t_h) => t_h
  end.

Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool
  := (v,s,t,s_h,t_h) \in st.

(* This relation links blocks (b,b') if b is an ancestor of b' and
   b' is at the next checkpoint level above b *)
Variable hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

(* The genesis block. Usually less interesting than
   the block which started the current epoch *)
Variable genesis : Hash.

Definition hash_ancestor h1 h2 :=
 connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

Lemma hash_ancestor_base : forall h1 h2,
  h1 <~ h2 -> h1 <~* h2.
Proof.
by apply/connect1.
Qed.

Lemma hash_ancestor_step : forall h1 h2 h3,
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
move => h1 h2 p H1 H2 Hp.
destruct H2.
move: Hp H1.
by apply/connect_trans.
Qed.

(* steps to ancestor is at least n *)
Inductive nth_ancestor : nat -> Hash -> Hash -> Prop :=
| nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
| nth_ancestor_nth : forall n h1 h2 h3,
    nth_ancestor n h1 h2 -> h2 <~ h3 ->
    nth_ancestor n.+1 h1 h3.

(* A validator may not make two votes with different target hashes at the same
  target height (whatever the source blocks)
 *)
Definition slashed_dbl_vote st v :=
  exists t1 t2, t1 <> t2 /\ exists s1 s1_h s2 s2_h t_h,
      vote_msg st v s1 t1 s1_h t_h /\ vote_msg st v s2 t2 s2_h t_h.

(* A validator may not make two votes with the source and target of one vote
   both strictly between the source and target of the other
 *)
Definition slashed_surround st v :=
  exists s1 t1 s1_h t1_h,
  exists s2 t2 s2_h t2_h,
    vote_msg st v s1 t1 s1_h t1_h /\
     vote_msg st v s2 t2 s2_h t2_h /\
     s2_h > s1_h /\ t2_h < t1_h.

Definition slashed st v : Prop :=
 slashed_dbl_vote st v \/ slashed_surround st v.

(* The finalized node at which the current epoch started *)
Variable epoch_start : Hash.
Variable epoch_height : nat.
Hypothesis epoch_ancestry : nth_ancestor epoch_height genesis epoch_start.

Definition link_supporters st s t s_h t_h : {set Validator} :=
  [set v | vote_msg st v s t s_h t_h ].
Definition justified_link (st:State) (s t : Hash) (s_h t_h : nat) : bool :=
  link_supporters st s t s_h t_h \in quorum_1.

Inductive justified_this_epoch (st:State) : Hash -> nat -> Prop :=
| epoch_justified : justified_this_epoch st epoch_start epoch_height
| justfied_link : forall s s_h t t_h,
    justified_this_epoch st s s_h ->
    s <~* t ->
    justified_link st s t s_h t_h ->
    justified_this_epoch st t t_h.

Lemma justified_is_descendant st n n_h:
  justified_this_epoch st n n_h -> epoch_start <~* n.
Proof.
  induction 1;[
    eapply connect0|
    eapply connect_trans; eassumption].
Defined.

Definition sources_justified st v :=
  forall s t s_h t_h,
    vote_msg st v s t s_h t_h ->
    epoch_start <~* s /\ justified_this_epoch st s s_h.

Definition one_third_slashed st :=
  exists q, q \in quorum_2 /\ forall v, v \in q -> slashed st v.

Definition one_third_bad st :=
  exists q, q \in quorum_2 /\ forall v, v \in q ->
   (slashed st v \/ ~ sources_justified st v).

Definition unslashed_can_extend st st' : Prop :=
  forall v s t s_h t_h,
    vote_msg st' v s t s_h t_h = true ->
    vote_msg st v s t s_h t_h = true \/ ~ slashed st v.

Definition no_new_slashed st st' :=
  forall v, slashed st' v -> slashed st v.

Definition blocks_exist_high_over (base : Hash) : Prop :=
  forall n, exists block, nth_ancestor n base block.

Definition highest_justified st b b_h : Prop :=
  forall b' b_h', b_h' >= b_h -> justified_this_epoch st b' b_h' -> b' = b /\ b_h' = b_h.

Lemma highest_exists: forall st,
    ~ one_third_bad st ->
    exists b b_h,
      justified_this_epoch st b b_h /\
      highest_justified st b b_h.
Admitted.

Definition highest (A : {fset nat}) : nat :=
  \max_(i : A) (val i).

Lemma highest_ub:
  forall (A : {fset nat}) (x:nat), x \in A -> x <= highest A.
Proof.
move => A x Hx.
case (insubP [subType of A] x) => /=; last by move: Hx =>->.
move => k Hk =><-.
exact: leq_bigmax_cond.
Qed.

Lemma two_thirds_good: forall st,
    ~ one_third_bad st ->
    exists (q : {set Validator}), q \in quorum_1 /\ forall v, v \in q ->
     (~ slashed st v /\ sources_justified st v).
Proof.
Admitted.

Lemma ltSnn: forall n, (n.+1 < n) = false.
Proof.
by move => n; apply/negP/negP; rewrite leqNgt; apply/negP; case/negP.
Qed.

Lemma plausible_liveness :
  forall st, ~ one_third_bad st ->
  (forall b b_h, highest_justified st b b_h -> blocks_exist_high_over b) ->
  exists st', unslashed_can_extend st st' /\ no_new_slashed st st'.
Proof.
  intros st Hgood Hheight.
  destruct (highest_exists Hgood) as (just_max & just_max_h & [Hjust_max_just Hjust_max_max]).
  specialize (Hheight _ _ Hjust_max_max).

  apply two_thirds_good in Hgood.
  destruct Hgood as (good_quorum & Hgood_is_quorum & Hgood).

  pose targets := (epoch_height |` [ fset vote_target_height vote | vote in st])%fset;
                    change {fset nat} in (type of targets).
  pose highest_target := highest targets.
  destruct (Hheight (highest_target.+2)) as [new_finalized Hpath].
  inversion Hpath;subst. rename h2 into new_final_parent.

  pose new_votes1 := [fset (v,just_max,new_final_parent,just_max_h,highest_target.+1)
                     | v in good_quorum]%fset; change {fset Vote} in (type of new_votes1).
  pose new_votes2 := [fset (v,new_final_parent,new_finalized,highest_target.+1,highest_target.+2)
                     | v in good_quorum]%fset; change {fset Vote} in (type of new_votes2).

  exists (st `|` new_votes1 `|` new_votes2)%fset.
  split.
  unfold unslashed_can_extend.

  clear -Hgood.
  unfold vote_msg.
  intros v s t s_h t_h.
  rewrite in_fsetU. rewrite in_fsetU.
  rewrite !Bool.orb_true_iff.
  move => [[H|H] | H];[tauto|right;apply Hgood..].
  case/imfsetP: H => x Hx Heq. replace v with x. assumption. congruence.
  case/imfsetP: H => x Hx Heq. replace v with x. assumption. congruence.

  pose proof (@highest_ub targets).
  assert (forall v s t s_h t_h, (v,s,t,s_h,t_h) \in st -> t_h <= highest_target)
    as H_st_highest by
   (clear;intros;apply highest_ub;
    apply/fsetUP;right;revert H;apply in_imfset).

  Local Ltac new_vote_mem_tac Hvote :=
    let x := fresh "x" in
    let x_good := fresh "x_good" in
    let Heq := fresh "Heq" in
    case/imfsetP: Hvote => x x_good Heq;injection Heq;clear Heq;intros;subst x;subst.
  assert (forall n n_h, justified_this_epoch st n n_h -> n_h <= highest_target)
    as Hjust_le_target by
     (clear -quorum_1_nonempty;intros n n_h H;
     apply highest_ub;destruct H;[by apply fset1U1|];
     destruct (quorum_1_nonempty H1) as [t_supporter Ht];
     rewrite in_set in Ht; apply/fsetUP; right;
     revert Ht; apply in_imfset).

  unfold no_new_slashed.
  intros badV [Hdbl|Hnest];[left|right].
  (* slashed for double vote *)
  unfold slashed_dbl_vote, vote_msg in Hdbl |- *.
  destruct Hdbl as (t1 & t2 & Hneq_t & Hdouble_votes).
  exists t1. exists t2. split;[exact Hneq_t|].
  destruct Hdouble_votes as (s1 & s1_h & s2 & s2_h & t_h & Hvote1 & Hvote2).
  exists s1; exists s1_h; exists s2; exists s2_h; exists t_h.

  rewrite in_fsetU in Hvote1;case/orP: Hvote1 => Hvote1.
  rewrite in_fsetU in Hvote1;case/orP: Hvote1 => Hvote1.
  split;[assumption|].
  apply H_st_highest in Hvote1.

  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  assumption.
  new_vote_mem_tac Hvote2.
  contradict Hvote1;clear. rewrite ltnn. trivial.
  new_vote_mem_tac Hvote2.
  contradict Hvote1;clear. rewrite ltSnn. trivial.

  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  split;[|assumption].
  apply H_st_highest in Hvote2.
  new_vote_mem_tac Hvote1.
  rewrite ltnn in Hvote2. solve[auto].

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  contradict Hneq_t. reflexivity.

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  contradict H2. solve[apply n_Sn].

  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  split;[|assumption].
  apply H_st_highest in Hvote2.
  new_vote_mem_tac Hvote1.
  contradict Hvote2;clear. rewrite ltSnn. trivial.

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  symmetry in H2. solve[case/n_Sn: H2].

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  clear -Hneq_t. congruence.

  (* slashed surround case *)
  unfold slashed_surround in Hnest |- *.
  destruct Hnest as (s1 & t1 & s1_h & t1_h & s2 & t2 & s2_h & t2_h & Hnest).
  exists s1;exists t1;exists s1_h;exists t1_h;exists s2;exists t2;exists s2_h;exists t2_h.
  destruct Hnest as (Houter & Hinner & Hstarts & Hends).
  rewrite <- and_assoc. split;[|split;assumption].

  unfold vote_msg in * |- *.
  rewrite in_fsetU in Houter;case/orP: Houter => Houter.
  rewrite in_fsetU in Houter;case/orP: Houter => Houter.
  split;[assumption|].
  apply H_st_highest in Houter.

  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  assumption.

  new_vote_mem_tac Hinner.
  clear -Hends Houter.
  assert (t1_h < t1_h) by (apply ltn_trans with (highest_target.+1);assumption).
  rewrite ltnn in H. contradict H. solve[trivial].

  new_vote_mem_tac Hinner.
  clear -Hends Houter.
  assert (t1_h < t1_h).
  apply ltn_trans with (highest_target.+1).
  assumption. apply ltn_trans with (highest_target.+2). apply ltnSn. assumption.
  contradict H. rewrite ltnn. solve[trivial].

  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  split;[|assumption].

  new_vote_mem_tac Houter.
  change (is_true (badV \in good_quorum)) in x_good.

  apply Hgood in x_good. destruct x_good as [Hnot_slashed Hsources_justified].
  apply Hsources_justified in Hinner. destruct Hinner as [_ Hst2_justified].
  clear -Hjust_max_max Hst2_justified Hstarts.
  apply Hjust_max_max in Hst2_justified;[|apply ltnW;assumption].
  destruct Hst2_justified.
  contradict Hstarts.
  rewrite -H0. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  contradict Hstarts. clear. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  contradict Hends. clear. rewrite ltSnn. trivial.

  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  split;[|assumption].

  new_vote_mem_tac Houter.
  apply Hgood in x_good. destruct x_good as [_ x_good].
  apply x_good in Hinner. destruct Hinner as [_ Hinner].
  apply Hjust_le_target in Hinner.
  clear -Hstarts Hinner.
  rewrite <- ltnS in Hinner.
  assert (s2_h < s2_h). apply ltn_trans with highest_target.+1;assumption.
  contradict H. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  exfalso.
  apply Hjust_le_target in Hjust_max_just.
  clear -Hjust_max_just Hstarts.
  rewrite <- ltnS in Hjust_max_just.
  assert (just_max_h < just_max_h).
  eapply ltn_trans;eassumption.
  contradict H. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  contradict Hstarts. clear.
  rewrite ltnn. trivial.
Qed.

End Liveness.
