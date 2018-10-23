From mathcomp
Require Import all_ssreflect.

From CasperToychain
Require Import ValidatorQuorum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DT.

Variable T : finType.

Variable d : T -> nat.

Definition gt_dset n : {set {set T}} :=
 [set x in powerset [set: T] | \sum_(t in x) (d t) >= n].

Lemma gt_dset_in : forall n (s : {set T}), \sum_(t in s) (d t) >= n = (s \in gt_dset n).
Proof.
move => n s.
rewrite inE andb_idl // => Hn.
by rewrite powersetE.
Qed.

Variable x y z : nat.

Local Notation bot := (((x * \sum_(t : T) (d t)) %/ y).+1).

Local Notation top := (((z * \sum_(t : T) (d t)) %/ y).+1).

Hypothesis constr : bot + \sum_(t : T) (d t) <= 2 * top.

Lemma d_disjoint_leq : forall (q1 q2 : {set T}),
 [disjoint q1 & q2] ->
 \sum_(t in q1) (d t) + \sum_(t in q2) (d t) <= \sum_(t : T) (d t).
Proof.
Admitted.

Lemma d_bot_top_intersection :
  forall q1 q2, q1 \in gt_dset top -> q2 \in gt_dset top ->
  exists q3, q3 \in gt_dset bot /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
Admitted.

End DT.

Section DTThirds.

Variable Validator : finType.

Variable deposit : Validator -> nat.

Definition deposit_ge_bot_validators :=
 ((\sum_(v : Validator) (deposit v)) %/ 3).+1.
Definition deposit_ge_top_validators :=
 ((2 * \sum_(v : Validator) (deposit v)) %/ 3).+1.

Definition deposit_bot_validators := gt_dset deposit deposit_ge_bot_validators.
Definition deposit_top_validators := gt_dset deposit deposit_ge_top_validators.

Lemma Validators_deposit_constr_thirds :
  ((1 * \sum_(v : Validator) (deposit v)) %/ 3).+1 + \sum_(v : Validator) (deposit v) <=
   2 * ((2 * \sum_(v : Validator) (deposit v)) %/ 3).+1.
Proof.
rewrite mul1n.
exact: constr_thirds.
Qed.

Lemma deposit_bot_top_validator_intersection :
  forall q1 q2, q1 \in deposit_top_validators -> q2 \in deposit_top_validators ->
  exists q3, q3 \in deposit_bot_validators /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have [q3 [Hq3 Hq3']] := d_bot_top_intersection Validators_deposit_constr_thirds Hq1 Hq2.
exists q3; split => //.
by rewrite mul1n in Hq3.
Qed.

End DTThirds.
