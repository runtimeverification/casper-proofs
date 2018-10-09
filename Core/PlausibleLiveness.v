From mathcomp
Require Import all_ssreflect.

From Hammer
Require Import Hammer Reconstr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Liveness.

Variable Validator : finType.
Variable Hash : finType.

Variable quorum_1 : {set {set Validator}}.
Variable quorum_2 : {set {set Validator}}.

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

Definition unslashed_can_extend (s s' : State) := True.

Definition no_new_slashed (s s' : State) := True.
  
Lemma plausible_liveness :
  forall s, ~ one_third_slashed s ->
  exists s', unslashed_can_extend s s' /\
  no_new_slashed s s'.
Proof.
Admitted.

(*
lemma plausible_liveness :
  "situation_has_finitely_many_validators s \<Longrightarrow>
   no_invalid_view s \<Longrightarrow>
   new_descendant_available s \<Longrightarrow>
   finite_messages s \<Longrightarrow>
   \<not> one_third_slashed s \<Longrightarrow>
   \<exists> s_new h_new.
     \<not> committed s h_new \<and>
     unslashed_can_extend s s_new \<and>
     committed s_new h_new \<and>
     no_new_slashed s s_new"
*)
End Liveness.
