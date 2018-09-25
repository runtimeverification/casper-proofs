Require Import mathcomp.ssreflect.ssreflect.
From Hammer
Require Import Hammer Reconstr.
Require Import Arith.
Require Import Omega.

Section Div.

Variable n : nat.

Hypothesis Hn: n <> 0.

Variables x y z : nat.

Hypothesis Hy: y <> 0.

Hypothesis twox : z + y <= 2 * x.

Lemma one : z * n + y * n <= 2 * x * n.
Proof.
have ->: z * n + y * n = n * (z + y) by ring.
have ->: (2 * x * n = n * (2 * x)) by ring.
by Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.mul_le_mono_nonneg_l, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.le_0_l) (@Coq.Init.Nat.double, @Coq.Arith.PeanoNat.Nat.b2n).
Qed.

Definition xn := (x * n) / y.
Definition zn := (z * n) / y.

Lemma two : zn + n <= 2 * xn.
Proof.
rewrite /zn /xn.
have bla :=  Nat.div_mul_le (x * n) y 2 Hy.
have Hzy: (z * n) * y / y <= y * z * n / y.
  by Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.mul_comm, @Coq.Arith.PeanoNat.Nat.mul_shuffle0, @Coq.Init.Peano.le_n) Reconstr.Empty.
rewrite Nat.div_mul // in Hzy.
suff Hsuff : y * ((z * n / y) + n) <= y * (2 * (x * n / y)).
  apply Nat.mul_le_mono_pos_l in Hsuff; auto with arith.
  by omega.
have Hone := one.
ring_simplify.
clear bla.
have Hp1: y * (z * n / y) <= S (z * n) by Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_succ_r, @Coq.Arith.PeanoNat.Nat.mul_div_le) Reconstr.Empty.
have Hs: y * (z * n / y) + y * n <= S (z * n) + y * n by apply plus_le_compat_r.
suff Hsuff: S (z * n) + y * n <= 2 * y * (x * n / y) by eapply le_trans in Hsuff; eauto.
clear Hs Hp1.
have Hle: 2 * (y * (x * n / y)) <= 2 * S (x * n).
  apply Nat.mul_le_mono_pos_l; auto.
  by Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_succ_r, @Coq.Arith.PeanoNat.Nat.mul_div_le) Reconstr.Empty.
Admitted.

End Div.

From mathcomp
Require Import all_ssreflect.

From CasperToychain
Require Import CasperOneMessage.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MT.

Variable T : finType.

Definition gt_cardset n : {set {set T}} := [set x in powerset [set: T] | #|x| >= n].

Lemma gt_cardset_in : forall n (s : {set T}), #|s| >= n = (s \in gt_cardset n).
Proof.
move => n s.
rewrite inE andb_idl // => Hn.
by rewrite powersetE.
Qed.

End MT.

Section Validators.

Variable Validator : finType.

Definition more_than_one_third := (#|Validator| %/ 3).+1.

Definition more_than_two_thirds := (2 * #|Validator| %/ 3).+1.

(*
Eval compute in (7 %/ 3).+1.
Eval compute in (2 * 4 %/ 3).+1.
*)

Definition Validators_2_3 : {set {set Validator}} := gt_cardset Validator more_than_two_thirds.

Definition Validators_1_3 : {set {set Validator}} := gt_cardset Validator more_than_one_third.

(* outline:
   - count number of elements in overlap
   - either overlap is greater than one third or it isn't
   - assume overlap is one third or less
   - show that 
   - suffices to show that number of elements in overlap is >= one third *)

Lemma Validators_third_quorums_intersection :
  forall q1 q2, q1 \in Validators_2_3 -> q2 \in Validators_2_3 ->
  exists q3, q3 \in Validators_1_3 /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have Hq1': #|q1| >= more_than_two_thirds by rewrite gt_cardset_in.
have Hq2': #|q2| >= more_than_two_thirds by rewrite gt_cardset_in.
have Hc1 := cardsC q1.
have Hc1' := cardsCs q1.
have Hc2 := cardsC q2.
have Hc2' := cardsCs q2.
rewrite /more_than_two_thirds in Hq1',Hq2'.
exists (q1 :&: q2).
split; last first.
  split; first by apply subsetIl.
  by apply subsetIr.
suff Hsuff: #|q1 :&: q2| >= more_than_one_third.
  rewrite inE.
  apply/andP; split => //.
  by rewrite inE.
rewrite /more_than_one_third.
clear Hq1 Hq2.
Admitted.

End Validators.
