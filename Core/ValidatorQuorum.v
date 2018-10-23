From mathcomp
Require Import all_ssreflect.

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
  have Hlt0: n' %% 3 > 0 by move: H3 Hlt; rewrite /dvdn; case Hn3: (n' %% 3).
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

Lemma disjoint_leq :
 forall (q1 q2 : {set T}), [disjoint q1 & q2] -> #|q1| + #|q2| <= #|T|.
Proof.
move => q1 q2.
rewrite disjoints_subset.
move => Hs.
have Hc2 := cardsC q2.
rewrite -Hc2.
have Hc := subset_leq_card Hs.
have ->: #|q2| + #|~: q2| = #|~: q2| + #|q2| by rewrite addnC.
by apply leq_add.
Qed.

Lemma bot_top_intersection :
  forall q1 q2, q1 \in gt_cardset top -> q2 \in gt_cardset top ->
  exists q3, q3 \in gt_cardset bot /\ q3 \subset q1 /\ q3 \subset q2.
Proof.
move => q1 q2 Hq1 Hq2.
have Hq1': #|q1| >= top by rewrite gt_cardset_in.
have Hq2': #|q2| >= top by rewrite gt_cardset_in.
exists (q1 :&: q2).
split; last by split; [apply subsetIl|apply subsetIr].
suff Hsuff: #|q1 :&: q2| >= bot by rewrite inE; apply/andP; split => //; rewrite inE.
clear Hq1 Hq2.
have Hq: 2 * ((z * #|T|) %/ y).+1 <= #|q1| + #|q2| by rewrite mul2n -addnn; apply leq_add => //=.
have Hle: ((x * #|T|) %/ y).+1 + #|T| <= #|q1| + #|q2| by eapply leq_trans; eauto.
have Hlt: (x * #|T|) %/ y + #|T| < #|q1| + #|q2| by [].
clear Hle Hq Hq1' Hq2'.
move: Hlt.
set lhs := _ %/ _.
move: lhs => n.
move => Hlt.
have Hlt': 0 < #|q1| + #|q2| by move:Hlt; case Hq: (#|q1| + #|q2|).
move: Hlt.
case Hc: ([disjoint q1 & q2]).
  move/disjoint_leq: Hc => Hc Hn.
  move: Hc.
  rewrite leqNgt.
  case/negP.  
  eapply leq_ltn_trans in Hn; eauto.
  by apply leq_addl.
rewrite -setI_eq0 in Hc.
have Hlt'': 0 < #|q1 :&: q2| by rewrite card_gt0; apply/eqP; move/eqP: Hc.
clear Hc.
have Hltt: #|q1| + #|q2| - #|q1 :&: q2| < #|q1| + #|q2|.  
  move: Hlt' Hlt''.
  set n1 := #|q1| + _.
  set n2 := #|_ :&: _|.
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
move/(@ltn_sub2r #|q1 :|: q2|).
rewrite {1}cardsU => Hlt.
move/Hlt: Hltt.
rewrite -cardsI.
have Hle: #|q1 :|: q2| <= #|T| by apply max_card.
rewrite -addnBA //.
set k := #|_| - _.
set l := #|_|.
move: k l.
clear Hlt.
elim => //=; first by move => l; rewrite addn0.
move => k IH l Hnk.
apply: IH.
move: Hnk.
rewrite addnS.
by move/ltnW.
Qed.
  
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
