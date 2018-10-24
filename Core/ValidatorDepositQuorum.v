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
      
Variable x y z : nat.

Local Notation bot := (((x * \sum_(t : T) (d t)) %/ y).+1).

Local Notation top := (((z * \sum_(t : T) (d t)) %/ y).+1).

Hypothesis constr : bot + \sum_(t : T) (d t) <= 2 * top.

Lemma d_disjoint_leq : forall (q1 q2 : {set T}),
 [disjoint q1 & q2] ->
 \sum_(t in q1) (d t) + \sum_(t in q2) (d t) <= \sum_(t : T) (d t).
Proof.
move => q1 q2 Hd.
rewrite -bigU //=.
rewrite big_mkcond /=.
apply: leq_sum.
move => t Ht.
by case: ifP.
Qed.

Lemma sum_all_gt_0_intersect :
  forall (q1 q2 : {set T}) n,
    0 < \sum_(t in q1) d t + \sum_(t in q2) d t ->
    n + \sum_(t in T) d t < \sum_(t in q1) d t + \sum_(t in q2) d t ->
    0 < \sum_(t in q1 :&: q2) (d t).
Proof.
Admitted.

Lemma sumU : forall (q1 q2 : {set T}),
    \sum_(t in (q1 :|: q2)) d t =
    \sum_(t in q1) (d t) + \sum_(t in q2) (d t) - \sum_(t in q1 :&: q2) (d t).
Proof.
Admitted.

Lemma sumI : forall (q1 q2 : {set T}),
  \sum_(t in q1 :&: q2) (d t) =
  \sum_(t in q1) (d t) + \sum_(t in q2) (d t) - \sum_(t in (q1 :|: q2)) d t.
Proof.
Admitted.
  
Lemma d_bot_top_intersection :
  forall q1 q2, q1 \in gt_dset top -> q2 \in gt_dset top ->
  exists q3, q3 \in gt_dset bot /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have Hq1': \sum_(t in q1) (d t) >= top by rewrite gt_dset_in.
have Hq2': \sum_(t in q2) (d t) >= top by rewrite gt_dset_in.
exists (q1 :&: q2).
split; last by split; [apply subsetIl|apply subsetIr].
suff Hsuff: \sum_(t in q1 :&: q2) (d t) >= bot by rewrite inE; apply/andP; split => //; rewrite inE.
clear Hq1 Hq2.
have Hq: 2 * ((z * \sum_(t in T) (d t)) %/ y).+1 <= \sum_(t in q1) (d t) + \sum_(t in q2) (d t).
  by rewrite mul2n -addnn; apply leq_add.
have Hle: ((x * \sum_(t in T) (d t)) %/ y).+1 + \sum_(t in T) (d t) <= \sum_(t in q1) (d t) + \sum_(t in q2) (d t) by eapply leq_trans; eauto.
have Hlt: (x * \sum_(t in T) (d t)) %/ y + \sum_(t in T) (d t) < \sum_(t in q1) (d t) + \sum_(t in q2) (d t) by [].
clear Hle Hq Hq1' Hq2'.
move: Hlt.
set lhs := _ %/ _.
move: lhs => n.
move => Hlt.
have Hlt': 0 < \sum_(t in q1) (d t) + \sum_(t in q2) (d t).
  by move:Hlt; case Hq: (\sum_(t in q1) (d t) + \sum_(t in q2) (d t)).
case Hc: ([disjoint q1 & q2]).
  move: Hlt.
  move/d_disjoint_leq: Hc => Hc Hn.
  move: Hc.
  rewrite leqNgt.
  case/negP.  
  eapply leq_ltn_trans in Hn; eauto.
  by apply leq_addl.
have Hlt'' := sum_all_gt_0_intersect Hlt' Hlt.
move: Hlt.  
have Hltt: \sum_(t in q1) (d t) + \sum_(t in q2) (d t) - \sum_(t in q1 :&: q2) (d t) <
  \sum_(t in q1) (d t) + \sum_(t in q2) (d t).
  move: Hlt' Hlt''.
  set n1 := \sum_(t in q1) (d t) + _.
  set n2 := \sum_(_ in _ :&: _) _.
  move: n1 n2.
  move => n1 n2 Hltn1 Htln2.
  case Heq: (n1 == n2); first by move/eqP: Heq =>->; rewrite subnn.
  move/orP: (leq_total n1 n2).
  case => Hn12; first by move: Hn12; rewrite -subn_eq0; move/eqP =>->.
  move: Hn12.
  rewrite leq_eqVlt.
  move/orP.
  case; first by rewrite eq_sym Heq.
  clear Heq Hltn1.
  move: n1 n2 Htln2.
  elim => //=.
  move => n0 IH.
  case => //=.
  case => //=; first by move => Hlt Hlt'; rewrite subnS.
  move => n1 Hlt Hltn.
  have Hlt0: 0 < n1.+1 by [].
  have Hlt1: n1.+1 < n0 by rewrite -(ltn_add2l 1) /=; rewrite 2!add1n.
  have IH' := IH n1.+1 Hlt0 Hlt1.
  rewrite subSn //=.
  have ->: n0.+1 = 1 + n0 by rewrite add1n.
  have ->: (n0 - n1.+2).+1 = 1 + (n0 - n1.+2) by rewrite add1n.
  rewrite ltn_add2l.
  suff Hsuff: n0 - n1.+2 <= n0 - n1.+1 by eapply leq_ltn_trans in Hsuff; eauto.
  by apply leq_sub2l.
move/(@ltn_sub2r (\sum_(t in q1 :|: q2) (d t))).
rewrite {1}sumU => Hlt.
move/Hlt: Hltt.
rewrite -sumI.
have Hle: \sum_(t in q1 :|: q2) (d t) <= \sum_(t in T) (d t).
  rewrite big_mkcond /=.
  apply: leq_sum.
  move => t Ht.
  by case: ifP.
rewrite -addnBA //.
set k := _ - _.
set l := \sum_(_ in _) _.
move: k l.
clear Hlt.
elim => //=; first by move => l; rewrite addn0.
move => k IH l Hnk.
apply: IH.
move: Hnk.
rewrite addnS.
by move/ltnW.
Qed.

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
