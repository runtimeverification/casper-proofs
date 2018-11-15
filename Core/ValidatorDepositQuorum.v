From mathcomp
Require Import all_ssreflect.
From Casper
Require Import ValidatorQuorum ssrAC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Proof of validator set intersection assumption for Casper accountable safety
   with 1/3 and 2/3 or more of all validators by deposit. *)

Lemma sum_rec4 :
 forall (K : nat -> nat -> nat -> nat -> Type),
 K 0 0 0 0 ->
 forall I r (P : pred I) F1 F2 F3 F4,
 (forall i y1 y2 y3 y4, P i -> K y1 y2 y3 y4 ->
   K ((F1 i) + y1) ((F2 i) + y2) ((F3 i) + y3) ((F4 i) + y4)) ->
  K (\sum_(i <- r | P i) F1 i)
    (\sum_(i <- r | P i) F2 i)
    (\sum_(i <- r | P i) F3 i)
    (\sum_(i <- r | P i) F4 i).
Proof.
move => K Kid I r P F1 F2 F3 F4 K_F.
by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F.
Qed.

Lemma all_sum_or_all (T : finType) (q : {set T}) F :
  \sum_(t in q :|: ~: q) F t =
  \sum_(t : T) F t.
Proof.
rewrite big_mkcond /=.
elim/big_ind2: _ => //=; first by move => x1 x2 y1 y2 =>->->.
move => t Ht.
case: ifP => Hf //.
move/negP: Hf.
case.
by rewrite setUCr.
Qed.

Lemma sum_ind4 :
 forall (K : nat -> nat -> nat -> nat -> Type),
 K 0 0 0 0 ->
 (forall x1 x2 x3 x4 y1 y2 y3 y4,
     K x1 x2 x3 x4 -> K y1 y2 y3 y4 -> K (x1 + y1) (x2 + y2) (x3 + y3) (x4 + y4)) ->
 forall (I : Type) (r : seq I) (P : pred I) (F1 : I -> nat) 
   (F2 : I -> nat) (F3 : I -> nat) (F4 : I -> nat),
   (forall i : I, P i -> K (F1 i) (F2 i) (F3 i) (F4 i)) ->
   K (\sum_(i <- r | P i) F1 i) (\sum_(i <- r | P i) F2 i)
     (\sum_(i <- r | P i) F3 i) (\sum_(i <- r | P i) F4 i).
Proof.
move => K Kid Kop.
move => I r P F1 F2 F3 F4 K_F.
apply: sum_rec4 => // i x1 x2 x3 x4 /K_F; apply: Kop.
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
- move => x1 x2 x3 y1 y2 y3 =>->->.
  rewrite 2!addnA.
  by rewrite (ACl addn (0 * 2 * 1 * 3)).
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

(* general proof without reference to 1/3 and 2/3 *)
Section DT.

Variable T : finType.

Variable d : T -> nat.

Definition gdset n : {set {set T}} :=
 [set x in powerset [set: T] | \sum_(t in x) (d t) >= n].

Lemma gt_dset_in : forall n (s : {set T}), \sum_(t in s) (d t) >= n = (s \in gdset n).
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

Lemma sumUI : forall (q1 q2 : {set T}),
    \sum_(t in (q1 :|: q2)) d t + \sum_(t in q1 :&: q2) (d t) =
    \sum_(t in q1) (d t) + \sum_(t in q2) (d t).
Proof.
move => q1 q2.
rewrite big_mkcond /=.
set s1 := \sum_i _.
rewrite big_mkcond /=.
set s2 := \sum_i _.
rewrite big_mkcond /=.
set s3 := \sum_i _.
rewrite big_mkcond /=.
set s4 := \sum_i _.
rewrite /s1 /s2 /s3 /s4 {s1 s2 s3 s4}.
elim/sum_rec4: _ => //=.
move => i y1 y2 y3 y4 Hi Hx.
case: ifP => //=; case: ifP => //=; case: ifP => //=; case: ifP => //=.
- move => _ _ _ _.
  set n := d i.
  move: n => n.
  rewrite addnA.
  rewrite (ACl addn (1 * 3 * 0 * 2)) Hx.  
  by rewrite (ACl addn (3 * 0 * (2 * 1))).
- move/negP => Hq1 Hq2.
  by move/setIP => [H1 H2].
- move => Hq2 /negP => Hq1.
  by move/setIP => [H1 H2].
- move/negP => Hq2 Hq1.
  by move/setIP => [H1 H2].
- move => Hq2 Hq1.
  by case/setIP.
- move => _ _ _ _.
  by rewrite 2!add0n -addnA Hx addnA.
- move => _ _ _ _.
  rewrite 2!add0n -addnA Hx.
  set n := d i.
  move: n => n.
  rewrite 2!addnA.
  by rewrite (ACl addn (1 * 0 * 2)).
- move/negP => Hq2 /negP => Hq1 Hq.
  by case/setUP.
- move => Hq2 Hq1 Hq.
  by case/setUP; left.
- move => Hq2 Hq1 Hq.
  by case/setUP; left.
- by move => Hq2 /negP => Hq1 /setIP => [[H1 H2]].
- by move/negP => Hq2 Hq1 /setIP => [[H1 H2]].
- by move => Hq2 Hq1; case/setIP.
- by move => Hq2 Hq1 _; case/setUP; left.
- by move => Hq2 _ _; case/setUP; right.
Qed.  
  
Lemma sumU : forall (q1 q2 : {set T}),
    \sum_(t in (q1 :|: q2)) d t =
    \sum_(t in q1) (d t) + \sum_(t in q2) (d t) - \sum_(t in q1 :&: q2) (d t).
Proof.
move => q1 q2.
by rewrite -sumUI addnK.
Qed.

Lemma sumI : forall (q1 q2 : {set T}),
  \sum_(t in q1 :&: q2) (d t) =
  \sum_(t in q1) (d t) + \sum_(t in q2) (d t) - \sum_(t in (q1 :|: q2)) d t.
Proof.
move => q1 q2.
by rewrite -sumUI addKn.
Qed.

Lemma add_ltn : forall n m p,
  n + m < p ->
  m < p.
Proof.
elim => //=.
move => n IH m p.
have Hn: n.+1 + m = n + m.+1 by rewrite addnS.
rewrite Hn => Hlt.
apply IH in Hlt.
move: Hlt.
by apply ltnW.
Qed.

Lemma sum_all_gt_0_intersect' :
  forall (q1 q2 : {set T}),
    \sum_(t in T) d t < \sum_(t in q1) d t + \sum_(t in q2) d t ->
    0 < \sum_(t in q1 :&: q2) (d t).
Proof.
move => q1 q2.  
rewrite -(all_sum_or_all q1) all_sum_or_a.
rewrite big_mkcond /=.
set s1 := \sum_i _.
rewrite big_mkcond /=.
set s2 := \sum_i _.
rewrite big_mkcond /=.
set s3 := \sum_i _.
rewrite big_mkcond /=.
rewrite /s1 /s2 /s3 {s1 s2 s3}.
elim/sum_rec4: _ => //=.
move => i y1 y2 y3 y4 Ht.
rewrite ltn_add2l => Hlt.
case: ifP => //=; case: ifP => //=; case: ifP => //=; case: ifP => //=.
- move => _ _ Hq1 Hq1'.
  by move/setCP: Hq1.
- move => _ _ Hq1 Hq1'.
  by move/setCP: Hq1.
- move/setIP => [H1 H2].
  by move/negP.
- move => _ _ Hq1 Hq2.
  by move/setCP: Hq1.
- move => _ _ _ _.
  rewrite add0n ltn_add2l.
  by case (d i).
- move/negP => Hq Hq2 _ Hq1.
  case: Hq.
  exact/setIP.
- move/setIP => [H1 H2].
  by move/negP.
- move => _ _ _ _.
  by rewrite 3!add0n ltn_add2l.
- move/setIP => [H1 H2] Hq2 _.
  by move/negP.
- move => _ _ _ _.
  by rewrite 2!add0n 2!ltn_add2l.
- move/setIP => [H1 H2].
  by move/negP.
- move => _ _ _ _.
  rewrite 3!add0n ltn_add2l => Hlt'.
  apply: Hlt.
  move: Hlt'.  
  exact: add_ltn.
- move/setIP => [H1 H2].
  move => _ _.
  by move/negP.
- move => _ _.
  move/setCP => Hq.
  move/negP => Hq'.
  by case: Hq.
- move => _ _.
  move/setCP => Hq.
  move/negP => Hq'.
  by case: Hq.
- move => _ _.
  move/setCP => Hq.
  move/negP => Hq'.
  by case: Hq.
Qed.

Lemma sum_all_gt_0_intersect :
  forall (q1 q2 : {set T}) n,
    n + \sum_(t in T) d t < \sum_(t in q1) d t + \sum_(t in q2) d t ->
    0 < \sum_(t in q1 :&: q2) (d t).
Proof.
move => q1 q2 n Hlt.
apply sum_all_gt_0_intersect' => //.
move: Hlt.
exact: add_ltn.
Qed.
  
Lemma d_bot_top_intersection :
  forall q1 q2, q1 \in gdset top -> q2 \in gdset top ->
  exists q3, q3 \in gdset bot /\ q3 \subset q1 /\ q3 \subset q2.
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
have Hlt'' := sum_all_gt_0_intersect Hlt.
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

(* instantiate above proof with 1/3 and 2/3 *)
Section DTThirds.

Variable Validator : finType.

Variable deposit : Validator -> nat.

Definition deposits := \sum_(v : Validator) (deposit v).

Definition deposit_bot := gdset deposit (deposits %/ 3).+1.

Definition deposit_top := gdset deposit ((2 * deposits) %/ 3).+1.

Lemma Validators_deposit_constr_thirds :
  ((1 * \sum_(v : Validator) (deposit v)) %/ 3).+1 + \sum_(v : Validator) (deposit v) <=
   2 * ((2 * \sum_(v : Validator) (deposit v)) %/ 3).+1.
Proof.
rewrite mul1n.
exact: constr_thirds.
Qed.

Lemma deposit_bot_top_validator_intersection :
  forall q1 q2, q1 \in deposit_top -> q2 \in deposit_top ->
  exists q3, q3 \in deposit_bot /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have [q3 [Hq3 Hq3']] := d_bot_top_intersection Validators_deposit_constr_thirds Hq1 Hq2.
exists q3; split => //.
by rewrite mul1n in Hq3.
Qed.

End DTThirds.
