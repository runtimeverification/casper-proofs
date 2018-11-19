From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This module proves the Plausible Liveness theorem for Casper
   from an abstract model of the blockchain and validator sets.
   Assumes a static set of validators.
 *)

Section Liveness.

(*
The background definitions of the block and validator structure
are based off of those from CasperOneMessage.v
 *)
Variable Validator : finType.
Variable Hash : finType.

(* The sets of "2/3 weight", these quorums are sufficient to justify a link *)
Variable quorum_1 : {set {set Validator}}.
(* The sets of "1/3 weight", proofs of safety show that a problem cannot
occur without a set of validators of this size getting slashed
 *)
Variable quorum_2 : {set {set Validator}}.

(* The essential intersection property that comes from the
   numeric choices 2/3 and 1/3 - and two sets from quorum_1
   have an intersection containing a quorum_2 set. *)
Hypothesis quorums_intersection :
  forall q1 q2, q1 \in quorum_1 -> q2 \in quorum_1 ->
  exists q3, q3 \in quorum_2 /\ q3 \subset q1 /\ q3 \subset q2.

(* For liveness proof we use additional assumptions that
   a supermajority quorum is nonempty, and that adding
   more validators to a supermajority leaves a supermajority
 *)
Hypothesis quorum_1_nonempty:
  forall q, q \in quorum_1 -> exists v, v \in q.
Hypothesis quorum_1_upclosed:
  forall (q1 q2:{set Validator}), q1 \subset q2 -> q1 \in quorum_1 -> q2 \in quorum_1.

(* Each vote names source and target nodes by giving hash and height,
   and is signed by a particular validator.

   This definition is different from votes in CasperOneMessage.v,
   this is taken directly from the way votes are expressed in the
   Casper paper.
 *)
Definition Vote := (Validator * Hash * Hash * nat * nat)%type.
(* A State is described by the set of votes case in the current epoch.
   For liveness we insist that this be a finite set of votes.
 *)
Definition State := {fset Vote}.
(* A boolean vote_msg predicate is then a definition rather than
   a field of State as in CasperOneMessage.v *)
Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool
  := (v,s,t,s_h,t_h) \in st.

(* This relation links blocks (b,b') if b is an ancestor of b' and
   b' is at the next checkpoint level above b *)
Variable hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

Definition hash_ancestor h1 h2 :=
 connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

(* We will need to use several property of ancestry
   inherited from the transitive closure operation "connect".
   We define these lemmas rather than unfolding the hash_ancestor
   definition inside other proofs.
 *)
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

(* This definition of ancestry makes the exact number of steps explicit *)
Inductive nth_ancestor : nat -> Hash -> Hash -> Prop :=
| nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
| nth_ancestor_nth : forall n h1 h2 h3,
    nth_ancestor n h1 h2 -> h2 <~ h3 ->
    nth_ancestor n.+1 h1 h3.

Lemma nth_ancestor_ancestor : forall n s t,
    nth_ancestor n s t -> (s <~* t).
Proof.
  induction 1.
  apply connect0.
  apply connect_trans with h2;[|apply connect1];assumption.
Qed.

(* Definitions of the slashing conditions *)
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

(* The genesis block. Usually less interesting than
   the block which started the current epoch *)
Variable genesis : Hash.
(* The finalized node at which the current epoch started. *)
Variable epoch_start : Hash.
Variable epoch_height : nat.
Hypothesis epoch_ancestry : nth_ancestor epoch_height genesis epoch_start.

(* Now we define justification *)
(* First a definition of supermajority links *)
Definition link_supporters st s t s_h t_h : {set Validator} :=
  [set v | vote_msg st v s t s_h t_h ].
Definition supermajority_link (st:State) (s t : Hash) (s_h t_h : nat) : bool :=
  link_supporters st s t s_h t_h \in quorum_1.

Lemma supermajority_weaken: forall (st st':State)
  (HSub:forall (v: Vote), v \in st -> v \in st'),
    forall s t s_h t_h,
      supermajority_link st s t s_h t_h
      -> supermajority_link st' s t s_h t_h.
Proof.
  move=> st st' Hsub s t s_h t_h.
  unfold supermajority_link, link_supporters, vote_msg.
  apply quorum_1_upclosed.
  apply/subsetP. intro. rewrite in_set. rewrite in_set.
  apply Hsub.
Qed.

(* We define justification in terms of a path from the epoch start,
   because the liveness proof is only concerned with with finalizing
   a further block.
 *)
Inductive justified_this_epoch (st:State) : Hash -> nat -> Prop :=
| epoch_justified : justified_this_epoch st epoch_start epoch_height
| justified_link : forall s s_h t t_h,
    justified_this_epoch st s s_h ->
    s <~* t ->
    supermajority_link st s t s_h t_h ->
    justified_this_epoch st t t_h.

(* Some properties of justification *)
Lemma justified_weaken: forall (st st':State)
    (HSub:forall (v: Vote), v \in st -> v \in st'),
  forall t t_h, justified_this_epoch st t t_h -> justified_this_epoch st' t t_h.
Proof.
  move=> st st' Hsub t t_h.
  induction 1. constructor.
  apply (justified_link IHjustified_this_epoch).
  assumption.
  revert H1.
  apply supermajority_weaken.
  assumption.
Qed.

Lemma justified_is_descendant st n n_h:
  justified_this_epoch st n n_h -> epoch_start <~* n.
Proof.
  induction 1;[
    eapply connect0|
    eapply connect_trans; eassumption].
Defined.

(* Now we begin making definitions used in the statement and proof of
   the plausible liveness theorem *)

(* The liveness theorem will assume that will assume that 2/3 of validators
   have not behaved badly. For liveness it is not sufficient to merely
   say they are unslashed.

   Votes with unjustified sources do not violate any slashing conditions
   themselves, but can prevent a validator from contributing to progress,
   because votes spanning over the unjustified vote would violate
   slashing condition II.
   No correct validator should ever make such a vote.

   We also simplify the problem by forbidding good validators from
   having votes with sources higher than the start of the current epoch
   but not descended from the current epoch.
   In the older casper design with Prepare/Commit messages this was
   prevented by slashing conditions.
 *)
Definition sources_justified st v :=
  forall s t s_h t_h,
    vote_msg st v s t s_h t_h ->
    epoch_start <~* s /\ justified_this_epoch st s s_h.

(* This assumption says 2/3 of the validators have behaved well *)
Definition two_thirds_good (st : State) :=
   exists (good_validators : {set Validator}), good_validators \in quorum_1 /\
  forall v, v \in good_validators -> (~ slashed st v /\ sources_justified st v).


(* We also need to assume block proposals continue.
   In particular, our proof requires that blocks exist
   sufficiently high over the highest justified block *)
Definition blocks_exist_high_over (base : Hash) : Prop :=
  forall n, exists block, nth_ancestor n base block.
(* We also define the property of being the highest justified block *)
Definition highest_justified st b b_h : Prop :=
  forall b' b_h', b_h' >= b_h
  -> justified_this_epoch st b' b_h'
  -> b' = b /\ b_h' = b_h.

(* We assume a highest justified block exists.
   This is left as an unproved assumption for now,
   becasue proving there is only one justified block
   of maximum height would require depending on
   the accountable safety theorem and assumptions of
   good behavior. *)
Lemma highest_exists: forall st,
    exists b b_h,
      justified_this_epoch st b b_h /\
      highest_justified st b b_h.
Admitted.

(** Now we have some defintions used to state the conclusion of the theorem **)
(* First, the solution only calls for votes from unslashed validators. *)
Definition unslashed_can_extend st st' : Prop :=
  forall v s t s_h t_h,
    vote_msg st' v s t s_h t_h = true ->
    vote_msg st v s t s_h t_h = true \/ ~ slashed st v.
(* Second, making the new votes does not cause any previously unslashed
   validator to be slashed *)
Definition no_new_slashed st st' :=
  forall v, slashed st' v -> slashed st v.


(** Now a few minor lemmas and definitions used in the proof **)
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

Lemma ltSnn: forall n, (n.+1 < n) = false.
Proof.
by move => n; apply/negP/negP; rewrite leqNgt; apply/negP; case/negP.
Qed.

Definition vote_target_height (v:Vote) : nat :=
  match v with
    (_,_,_,_,t_h) => t_h
  end.

(** And finally, the overall plausible liveness theorem **)
Lemma plausible_liveness :
  forall st, two_thirds_good st ->
  (forall b b_h, highest_justified st b b_h -> blocks_exist_high_over b) ->
  exists st', unslashed_can_extend st st' /\ no_new_slashed st st' /\
              exists (new_finalized new_final_parent:Hash) new_height,
                justified_this_epoch st' new_final_parent new_height
                  /\ new_final_parent <~ new_finalized
                  /\ supermajority_link st' new_final_parent new_finalized
                                              new_height new_height.+1.
Proof.
  intros st Hgood Hheight.
  destruct (highest_exists st) as (just_max & just_max_h & [Hjust_max_just Hjust_max_max]).
  specialize (Hheight _ _ Hjust_max_max).

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
  split;[|split].

  *
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

  *
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
  apply x_good in Hinner. destruct Hinner as [_ Hs2_justified].
  apply Hjust_le_target in Hs2_justified.
  clear -Hstarts Hs2_justified.
  rewrite <- ltnS in Hs2_justified.
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

  * exists new_finalized. exists new_final_parent. exists (highest_target.+1).
    split.

    apply (@justified_link _ just_max just_max_h).
      revert Hjust_max_just. apply justified_weaken.
      apply/fsubsetP. by eapply fsubset_trans;apply fsubsetUl.

    revert H0. by apply nth_ancestor_ancestor.

    unfold supermajority_link, link_supporters, vote_msg.
    apply quorum_1_upclosed with good_quorum;[|assumption].
    apply /subsetP.
    intros v Hv_good.
    rewrite in_set. rewrite in_fsetU.
    apply/orP. left. rewrite in_fsetU.
    apply/orP. right. unfold new_votes1.
    apply/imfsetP. exists v.
      assumption. reflexivity.

    split. assumption.

    unfold supermajority_link, link_supporters, vote_msg.
    apply quorum_1_upclosed with good_quorum;[|assumption].
    apply /subsetP.
    intros v Hv_good.
    rewrite in_set. rewrite in_fsetU.
    apply/orP. right. unfold new_votes2.
    apply/imfsetP. exists v.
      assumption. reflexivity.
Qed.

End Liveness.