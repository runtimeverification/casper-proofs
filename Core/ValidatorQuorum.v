Require Import mathcomp.ssreflect.all_ssreflect.
From Hammer
Require Import Hammer Reconstr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Thirds.

Variable n : nat.

Lemma constr_thirds : (n %/ 3).+1 + n <= 2 * (2 * n %/ 3).+1.
Proof.
destruct n => //.
set n' := n0.+1.
have Hn': 0 < n' by [].
move: n' Hn' => n' Hn'.
rewrite -(@leq_pmul2l 3) //=.
rewrite mulnDr /=.
rewrite mulnS.
case H3: (3 %| n').
- rewrite muln_divCA //=.
  rewrite divnn //= muln1.
  rewrite mulnCA.
  rewrite mulnS.
  rewrite muln_divCA //=; last by rewrite dvdn_mull.
  rewrite divnn //= muln1.
  rewrite mulnDr /=.
  have ->: 2 * (2 * n') = 4 * n' by rewrite mulnA.
  have ->: 3 + n' + 3 * n' = 3 + 4 * n' by [].
  have ->: 2 * 3 = 6 by [].
  by apply leq_add.
- have Hlt: n' %% 3 < 3 by rewrite ltn_mod.
  have Hlt0: n' %% 3 > 0.
    move: H3 Hlt.
    rewrite /dvdn.
    by case Hn3: (n' %% 3).
  rewrite mulnS mulnDr.
  rewrite {2}(divn_eq n' 3) /= mulnDr.
  have ->: 3 * (n' %/ 3 * 3) = 3 * 3 * (n' %/ 3).
    rewrite mulnC.
    rewrite -(mulnC 3 (n' %/ 3)).
    by rewrite -(mulnAC 3 (n' %/ 3)).
  set lhs := _ + _.
  rewrite mulnA.
  have ->: 3 * 2 = 6 by [].
  rewrite (divn_eq n' 3).
  rewrite mulnDr.
  rewrite mulnA.
  have ->: 2 * (n' %/ 3) * 3 = 6 * (n' %/ 3) by rewrite mulnAC.
  case Hn3: (n' %% 3 == 1).
  * move/eqP: Hn3 => Hn3.
    rewrite Hn3.
    have ->: 2 * 1 = 2 by [].
    rewrite divnDl; last by apply dvdn_mulr.
    have ->: 2 %/ 3 = 0 by [].
    rewrite addn0.
    rewrite muln_divA; last by apply dvdn_mulr.
    have ->: (6 * (6 * (n' %/ 3))) = (3 * (2 * (6 * (n' %/ 3)))) by rewrite (mulnA 3).
    rewrite mulKn //.
    rewrite mulnA.
    have ->: 2 * 6 = 12 by [].
    rewrite /lhs Hn3.
    have ->: 3 * 3 = 9 by [].
    rewrite muln1.
    rewrite mulnC.
    have ->: 9 * (n' %/ 3) + 3 = 3 + 9 * (n' %/ 3) by rewrite addnC.
    rewrite addnA -addnC.
    have ->: 3 + n' %/ 3 * 3 + 3 = 3 * (n' %/ 3) + 6.
      rewrite addnC addnA.
      have ->: 3 + 3 = 6 by [].
      rewrite mulnC.
      by rewrite addnC.
    rewrite addnA.
    rewrite -mulnDl.
    have ->: 9 + 3 = 12 by [].
    by rewrite addnC.
  * move/eqP: Hn3 => Hn3.
    case Hn3': (n' %% 3 == 2).
    + move/eqP: Hn3' => Hn3'.
      rewrite Hn3'.
      have ->: 2 * 2 = 4 by [].
      rewrite divnDl; last by apply dvdn_mulr.
      have ->: 4 %/ 3 = 1 by [].
      rewrite mulnDr muln1.
      rewrite muln_divA; last by apply dvdn_mulr.
      have ->: (6 * (6 * (n' %/ 3))) = (3 * (2 * (6 * (n' %/ 3)))) by rewrite (mulnA 3).
      rewrite mulKn //.
      rewrite mulnA.
      have ->: 2 * 6 = 12 by [].
      rewrite /lhs Hn3'.
      have ->: 3 * 3 = 9 by [].
      have ->: 3 * 2 = 6 by [].
      rewrite mulnC.
      have ->: 9 * (n' %/ 3) + 6 = 6 + 9 * (n' %/ 3) by rewrite addnC.
      rewrite addnA -addnC.
      have ->: 3 + n' %/ 3 * 3 + 6 = 3 * (n' %/ 3) + 9.
        rewrite addnC addnA.
        have ->: 6 + 3 = 9 by [].
        rewrite mulnC.
        by rewrite addnC.
      rewrite addnA.
      rewrite -mulnDl.
      have ->: 9 + 3 = 12 by [].
      rewrite addnA.
      rewrite addnC.
      have ->: 6 + 12 * (n' %/ 3) + 6 = 12 + 12 * (n' %/ 3) by rewrite addnC addnA.
      by apply leq_add.
    + move/eqP: Hn3' => Hn3'.
      destruct (n' %% 3) => //.
      destruct n1 => //.
      by destruct n1.
Qed.

End Thirds.

Section MT.

Variable T : finType.

Definition gt_cardset n : {set {set T}} := [set x in powerset [set: T] | #|x| >= n].

Lemma gt_cardset_in : forall n (s : {set T}), #|s| >= n = (s \in gt_cardset n).
Proof.
move => n s.
rewrite inE andb_idl // => Hn.
by rewrite powersetE.
Qed.

Variable x y z : nat.

Local Notation bot := ((x * #|T| %/ y).+1).

Local Notation top := ((z * #|T| %/ y).+1).

Hypothesis constr : bot + #|T| <= 2 * top.

Lemma bot_top_intersection :
  forall q1 q2, q1 \in gt_cardset top -> q2 \in gt_cardset top ->
  exists q3, q3 \in gt_cardset bot /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have Hq1': #|q1| >= top by rewrite gt_cardset_in.
have Hq2': #|q2| >= top by rewrite gt_cardset_in.
have Hc1 := cardsC q1.
have Hc1' := cardsCs q1.
have Hc2 := cardsC q2.
have Hc2' := cardsCs q2.
exists (q1 :&: q2).
split; last first.
  split; first by apply subsetIl.
  by apply subsetIr.
suff Hsuff: #|q1 :&: q2| >= bot.
  rewrite inE.
  apply/andP; split => //.
  by rewrite inE.
clear Hq1 Hq2.
have Hq: 2 * ((z * #|T|) %/ y).+1 <= #|q1| + #|q2|.
  rewrite mul2n -addnn.
  by apply leq_add => //=.
Admitted.
  
End MT.

Section MTThirds.

Variable Validator : finType.

Definition ge_bot_validators := (#|Validator| %/ 3).+1.
Definition ge_top_validators := (2 * #|Validator| %/ 3).+1.

Definition bot_validators := gt_cardset Validator ge_bot_validators.
Definition top_validators := gt_cardset Validator ge_top_validators.

Lemma Validators_constr_thirds : (1 * #|Validator| %/ 3).+1 + #|Validator| <= 2 * (2 * #|Validator| %/ 3).+1.
Proof.
rewrite mul1n.
exact: constr_thirds.
Qed.

Lemma bot_top_validator_intersection :
  forall q1 q2, q1 \in top_validators -> q2 \in top_validators ->
  exists q3, q3 \in bot_validators /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have [q3 [Hq3 Hq3']] := bot_top_intersection Validators_constr_thirds Hq1 Hq2.
exists q3; split => //.
by rewrite mul1n in Hq3.
Qed.
  
End MTThirds.
