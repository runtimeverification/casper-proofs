From mathcomp
Require Import all_ssreflect.

From CasperToychain
Require Import ValidatorQuorum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subeq_tin : forall (T : finType) (q : {set T}) F,
 \sum_(t in q) (F t) = \sum_(t in q) (if t \in q then F t else 0).
Proof.
move => T q F.
apply eq_big => //.
by move => t; case: ifP.
Qed.

Lemma subeq_tinn (T : finType) (q : {set T}) F :
 \sum_(t in ~: q) (if t \in q then F t else 0) = 0.
Proof.
elim/big_ind: _ => //.
- by move => x y =>->->.
- move => t; case: ifP => //=.
  move => Ht.
  by move/setCP.
Qed.

Lemma all_sum_or (T : finType) (q : {set T}) F :
 \sum_(t in q :|: ~: q) F t =     
 \sum_(t : T | ((t \in q) || (t \in ~: q))) F t.
Proof.
apply: eq_big => //.
by move => x; rewrite in_setU.
Qed.

Lemma subeq (T : finType) (q : {set T}) F :
 \sum_(t in q) (F t) = \sum_(t : T) (if t \in q then F t else 0).
Proof.
by rewrite big_mkcond.
Qed.

Lemma all_sum_or_all (T : finType) (q : {set T}) F :
  \sum_(t in q :|: ~: q) F t =
  \sum_(t : T) F t.
Proof.
rewrite subeq.
elim/big_ind2: _ => //=; first by move => x1 x2 y1 y2 =>->->.
move => t Ht.
case: ifP => Hf //.
move/negP: Hf.
case.
by rewrite setUCr.
Qed.

Lemma all_sum_or_a (T : finType) (q : {set T}) F :
  \sum_(t in q :|: ~: q) F t =
  \sum_(t in q) F t + \sum_(t in ~: q) F t.
Proof.
rewrite big_mkcond /=.
set s := \sum_i _.
rewrite big_mkcond /=.
set s1 := \sum_i _.
rewrite big_mkcond /=.
rewrite /s /s1 {s s1}.
elim/big_ind3: _ => //=.
- move => x1 x2 x3 y1 y2 y3 Hx Hy.
  set s := _ + _.
  rewrite addnC addnA.
  rewrite -addnC.
  rewrite -addnA.
  rewrite addnC.
  have ->: y1 + x2 = x2 + y1 by rewrite addnC.
  rewrite addnA.
  have ->: x1 + x2 = x2 + x1 by rewrite addnC.
  rewrite -Hx.
  rewrite addnC.
  rewrite addnA.
  rewrite addnC.
  rewrite addnA.
  have ->: y1 + y2 = y2 + y1 by rewrite addnC.
  rewrite -Hy.
  by rewrite addnC.
- move => t Ht.
  case: ifP; case: ifP; case: ifP => //=.
  * by move/setCP.
  * move/negP => Hn.
    move/negP => Hn'.
    by move/setUP; case.
  * move => Hn Hn'.
    move/setUP.
    by case; left.
  * move => Hn Hn'.
    move/setUP.
    by case; left.
  * move => Hn Hn'.
    move/setUP.
    by case; right.
Qed.

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

(*
Lemma all_sum_split : forall (q : {set T}) F, 
 \sum_(t : T) F t = \sum_(t in q :|: ~: q) F t.
Proof.
move => q F.
*)

(*
Lemma subeq : forall (q : {set T}),
 \sum_(t in q) (d t) = \sum_(t : T) (if t \in q then d t else 0).
Proof.
move => q.  
rewrite subeq_tin.
elim/big_rec2: _.
apply: congr_big => //.
move => x0.
*)
      
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
