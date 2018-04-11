From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype finset.
From mathcomp
Require Import path.
Require Import Eqdep.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
Set Implicit Arguments.
From CasperToychain
Require Import Blockforest.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record EpochData :=
  mkEpochData {
    epoch_target_hash : Hash;
    epoch_voted : seq ValidatorIndex;
    epoch_curr_dyn_votes : union_map [ordType of Epoch] Wei;
    epoch_prev_dyn_votes : union_map [ordType of Epoch] Wei;
    epoch_is_justified : bool;
    epoch_is_finalized : bool
  }.

Record ValidatorData :=
  mkValidatorData {
    validator_addr : Address;
    validator_withdrawal_addr : Address;
    validator_deposit : union_map [ordType of Epoch] Wei;
    validator_start_dynasty : Dynasty;
    validator_end_dynasty : Dynasty
  }.

Record CasperData :=
  mkCasperData {
    casper_epochs : union_map [ordType of Epoch] EpochData;
    casper_validators : union_map [ordType of ValidatorIndex] ValidatorData;
    casper_current_dynasty: Dynasty;
    casper_current_epoch : Epoch;
    casper_expected_target_hash : Hash;
    casper_expected_source_epoch : Epoch;
    casper_last_justified_epoch : Epoch;
    casper_last_finalized_epoch : Epoch;
    casper_dynasty_start_epoch : union_map [ordType of Dynasty] Epoch;
    casper_total_curr_dyn_deposits : Wei;
    casper_total_prev_dyn_deposits : Wei;
    casper_next_validator_index : ValidatorIndex
  }.

Definition eq_EpochData (e e' : EpochData) :=
  match e, e' with
  | mkEpochData h1 v1 cv1 pv1 j1 f1, mkEpochData h2 v2 cv2 pv2 j2 f2 =>
    [&& h1 == h2, v1 == v2, cv1 == cv2, pv1 == pv2, j1 == j2 & f1 == f2]
  end.

Lemma eq_EpochDataP : Equality.axiom eq_EpochData.
Proof.
case => h1 v1 cv1 pv1 j1 f1; case => h2 v2 cv2 pv2 j2 f2; rewrite /eq_EpochData /=.
case H2: (h1 == h2); [move/eqP: H2=>?; subst h2| constructor 2];
  last by case=>?; subst h2;rewrite eqxx in H2.
case H3: (v1 == v2); [move/eqP: H3=>?; subst v2| constructor 2];
  last by case=>?; subst v2;rewrite eqxx in H3.
case H4: (cv1 == cv2); [move/eqP: H4=>?; subst cv2| constructor 2];
  last by case=>?; subst cv2;rewrite eqxx in H4.
case H5: (pv1 == pv2); [move/eqP: H5=>?; subst pv2| constructor 2];
  last by case=>?; subst pv2;rewrite eqxx in H5.
case H6: (j1 == j2); [move/eqP: H6=>?; subst j2| constructor 2];
  last by case=>?; subst j2;rewrite eqxx in H6.
case H7: (f1 == f2); [move/eqP: H7=>?; subst f2| constructor 2];
  last by case=>?; subst f2;rewrite eqxx in H7.
by constructor 1.
Qed.

Definition EpochData_eqMixin :=
  Eval hnf in EqMixin eq_EpochDataP.
Canonical EpochData_eqType :=
  Eval hnf in EqType EpochData EpochData_eqMixin.

Definition eq_ValidatorData (v v' : ValidatorData) :=
match v, v' with
| mkValidatorData a1 aw1 d1 sd1 ed1, mkValidatorData a2 aw2 d2 sd2 ed2 =>
  [&& a1 == a2, aw1 == aw2, d1 == d2, sd1 == sd2 & ed1 == ed2]
end.

Lemma eq_ValidatorDataP : Equality.axiom eq_ValidatorData.
Proof.
case => a1 aw1 d1 sd1 ed1; case => a2 aw2 d2 sd2 ed2; rewrite /eq_ValidatorData/=.
case H1: (a1 == a2); [move/eqP: H1=>?; subst a1| constructor 2];
  last by case=>?; subst a2;rewrite eqxx in H1.
case H2: (aw1 == aw2); [move/eqP: H2=>?; subst aw2| constructor 2];
  last by case=>?; subst aw2;rewrite eqxx in H2.
case H3: (d1 == d2); [move/eqP: H3=>?; subst d2| constructor 2];
  last by case=>?; subst d2;rewrite eqxx in H3.
case H4: (sd1 == sd2); [move/eqP: H4=>?; subst sd2| constructor 2];
  last by case=>?; subst sd2;rewrite eqxx in H4.
case H5: (ed1 == ed2); [move/eqP: H5=>?; subst ed2| constructor 2];
  last by case=>?; subst ed2;rewrite eqxx in H5.
by constructor 1.
Qed.

Definition ValidatorData_eqMixin :=
  Eval hnf in EqMixin eq_ValidatorDataP.
Canonical ValidatorData_eqType :=
  Eval hnf in EqType ValidatorData ValidatorData_eqMixin.

Definition eq_CasperData (c c' : CasperData) :=
match c, c' with
| mkCasperData e1 v1 cd1 ce1 eth1 ese1 lje1 lfe1 dse1 tcdd1 tpdd1 nvi1,
  mkCasperData e2 v2 cd2 ce2 eth2 ese2 lje2 lfe2 dse2 tcdd2 tpdd2 nvi2 =>
  [&& e1 == e2, v1 == v2, cd1 == cd2, ce1 == ce2, eth1 == eth2, ese1 == ese2,
   lje1 == lje2, lfe1 == lfe2, dse1 == dse2, tcdd1 == tcdd2, tpdd1 == tpdd2 & nvi1 == nvi2]
end.

Lemma eq_CasperDataP : Equality.axiom eq_CasperData.
Proof.
case => e1 v1 cd1 ce1 eth1 ese1 lje1 lfe1 dse1 tcdd1 tpdd1 nvi1.
case => e2 v2 cd2 ce2 eth2 ese2 lje2 lfe2 dse2 tcdd2 tpdd2 nvi2.
rewrite /eq_CasperData/=.
case H2: (e1 == e2); [move/eqP: H2=>?; subst e2| constructor 2];
  last by case=>?; subst e2;rewrite eqxx in H2.
case H3: (v1 == v2); [move/eqP: H3=>?; subst v2| constructor 2];
  last by case=>?; subst v2;rewrite eqxx in H3.
case H4: (cd1 == cd2); [move/eqP: H4=>?; subst cd2| constructor 2];
  last by case=>?; subst cd2;rewrite eqxx in H4.
case H5: (ce1 == ce2); [move/eqP: H5=>?; subst ce2| constructor 2];
  last by case=>?; subst ce2;rewrite eqxx in H5.
case H6: (eth1 == eth2); [move/eqP: H6=>?; subst eth2| constructor 2];
  last by case=>?; subst eth2;rewrite eqxx in H6.
case H7: (ese1 == ese2); [move/eqP: H7=>?; subst ese1| constructor 2];
  last by case=>?; subst ese2;rewrite eqxx in H7.
case H8: (lje1 == lje2); [move/eqP: H8=>?; subst lje2| constructor 2];
  last by case=>?; subst lje2;rewrite eqxx in H8.
case H9: (lfe1 == lfe2); [move/eqP: H9=>?; subst lfe2| constructor 2];
  last by case=>?; subst lfe2;rewrite eqxx in H9.
case H10: (dse1 == dse2); [move/eqP: H10=>?; subst dse2| constructor 2];
  last by case=>?; subst dse2;rewrite eqxx in H10.
case H11: (tcdd1 == tcdd2); [move/eqP: H11=>?; subst tcdd2| constructor 2];
  last by case=>?; subst tcdd2;rewrite eqxx in H11.
case H12: (tpdd1 == tpdd2); [move/eqP: H12=>?; subst tpdd2| constructor 2];
  last by case=>?; subst tpdd2;rewrite eqxx in H12.
case H13: (nvi1 == nvi2); [move/eqP: H13=>?; subst nvi2| constructor 2];
  last by case=>?; subst nvi2;rewrite eqxx in H13.
by constructor 1.
Qed.

Definition CasperData_eqMixin :=
  Eval hnf in EqMixin eq_CasperDataP.
Canonical CasperData_eqType :=
  Eval hnf in EqType CasperData CasperData_eqMixin.

Definition InitCasperData :=
  {| casper_epochs := Unit;
     casper_validators := Unit;
     casper_current_dynasty := 0;
     casper_current_epoch := 0;
     casper_expected_target_hash := #GenesisBlock;
     casper_expected_source_epoch := 0;
     casper_last_justified_epoch := 0;
     casper_last_finalized_epoch := 0;
     casper_dynasty_start_epoch := Unit;
     casper_total_curr_dyn_deposits := 0;
     casper_total_prev_dyn_deposits := 0;
     casper_next_validator_index := 0
  |}.

Parameter casper_min_deposit_size : Wei.
Parameter casper_default_end_dynasty : Dynasty.
