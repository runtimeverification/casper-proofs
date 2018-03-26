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

Definition Account_ordMixin := fin_ordMixin Account.
Canonical Account_ordType : ordType := Eval hnf in OrdType Account Account_ordMixin.

Record ValidatorData :=
  mkValidator {
    va_deposit : nat;
    va_start_dynasty : Dynasty;
    va_end_dynasty : Dynasty
  }.

Definition eq_ValidatorData (v v' : ValidatorData) :=
  match v, v' with
  | mkValidator d1 sd1 ed1, mkValidator d2 sd2 ed2 =>
    [&& d1 == d2, sd1 == sd2 & ed1 == ed2]
  end.

Lemma eq_ValidatorDataP : Equality.axiom eq_ValidatorData.
Proof.
case => d1 sd1 ed1; case => d2 sd2 ed2; rewrite /eq_ValidatorData/=.
case H2: (d1 == d2); [move/eqP: H2=>?; subst d2| constructor 2];
  last by case=>?; subst d2;rewrite eqxx in H2.
case H3: (sd1 == sd2); [move/eqP: H3=>?; subst sd2| constructor 2];
  last by case=>?; subst sd2;rewrite eqxx in H3.
case H4: (ed1 == ed2); [move/eqP: H4=>?; subst ed2| constructor 2];
  last by case=>?; subst ed2;rewrite eqxx in H4.
by constructor 1.
Qed.

Definition ValidatorData_eqMixin :=
  Eval hnf in EqMixin eq_ValidatorDataP.
Canonical ValidatorData_eqType :=
  Eval hnf in EqType ValidatorData ValidatorData_eqMixin.

Record VotesData :=
  mkVotes {
    vo_cur_dyn_votes : nat;
    vo_prev_dyn_votes : nat;
    vo_vote_map : union_map Hash {set Address};
    vo_is_justified : bool;
    vo_is_finalized : bool
  }.

Definition eq_VotesData (v v' : VotesData) :=
  match v, v' with
  | mkVotes cdv1 pdv1 vm1 ij1 if1, mkVotes cdv2 pdv2 vm2 ij2 if2 =>
    [&& cdv1 == cdv2, pdv1 == pdv2, vm1 == vm2, ij1 == ij2 & if1 == if2]
  end.

Lemma eq_VotesDataP : Equality.axiom eq_VotesData.
Proof.
case => cdv1 pdv1 vm1 ij1 if1; case => cdv2 pdv2 vm2 ij2 if2; rewrite /eq_VotesData/=.
case H2: (cdv1 == cdv2); [move/eqP: H2=>?; subst cdv2| constructor 2];
  last by case=>?; subst cdv2;rewrite eqxx in H2.
case H3: (pdv1 == pdv2); [move/eqP: H3=>?; subst pdv2| constructor 2];
  last by case=>?; subst pdv2;rewrite eqxx in H3.
case H4: (vm1 == vm2); [move/eqP: H4=>?; subst vm2| constructor 2];
  last by case=>?; subst vm2;rewrite eqxx in H4.
case H5: (ij1 == ij2); [move/eqP: H5=>?; subst ij2| constructor 2];
  last by case=>?; subst ij2;rewrite eqxx in H5.
case H6: (if1 == if2); [move/eqP: H6=>?; subst if2| constructor 2];
  last by case=>?; subst if2;rewrite eqxx in H6.
by constructor 1.
Qed.

Definition VotesData_eqMixin :=
  Eval hnf in EqMixin eq_VotesDataP.
Canonical VotesData_eqType :=
  Eval hnf in EqType VotesData VotesData_eqMixin.

Record CasperData :=
  mkCasper {
    tr_validators : union_map [ordType of Account] ValidatorData;
    tr_checkpoint_hashes : union_map Epoch Hash;
    tr_dynasty : Dynasty;
    tr_next_dynasty_wei : nat;
    tr_second_next_dynasty_wei : nat;
    tr_total_curdyn_deposits: nat;
    tr_total_prevdyn_deposits: nat;
    tr_dynasty_start_epoch : union_map Dynasty Epoch;
    tr_dynasty_in_epoch : union_map Epoch Dynasty;
    tr_votes : union_map Epoch VotesData;
    tr_main_hash_justified : bool
  }.

Definition eq_CasperData (c c' : CasperData) :=
  match c, c' with
  | mkCasper va1 ch1 d1 ndw1 sndw1 tcd1 tpd1 dse1 die1 vo1 mh1, mkCasper va2 ch2 d2 ndw2 sndw2 tcd2 tpd2 dse2 die2 vo2 mh2 =>
    [&& va1 == va2, ch1 == ch2, d1 == d2, ndw1 == ndw2, sndw1 == sndw2, tcd1 == tcd2, tpd1 == tpd2, dse1 == dse2, die1 == die2, vo1 == vo2 & mh1 == mh2]
  end.

Lemma eq_CasperDataP : Equality.axiom eq_CasperData.
Proof.
case => va1 ch1 d1 ndw1 sndw1 tcd1 tpd1 dse1 die1 vo1 mh1; case => va2 ch2 d2 ndw2 sndw2 tcd2 tpd2 dse2 die2 vo2 mh2; rewrite /eq_CasperData/=.
case H2: (va1 == va2); [move/eqP: H2=>?; subst va2| constructor 2];
  last by case=>?; subst va2;rewrite eqxx in H2.
case H3: (ch1 == ch2); [move/eqP: H3=>?; subst ch2| constructor 2];
  last by case=>?; subst ch2;rewrite eqxx in H3.
case H4: (d1 == d2); [move/eqP: H4=>?; subst d2| constructor 2];
  last by case=>?; subst d2;rewrite eqxx in H4.
case H5: (ndw1 == ndw2); [move/eqP: H5=>?; subst ndw2| constructor 2];
  last by case=>?; subst ndw2;rewrite eqxx in H5.
case H6: (sndw1 == sndw2); [move/eqP: H6=>?; subst sndw2| constructor 2];
  last by case=>?; subst sndw2;rewrite eqxx in H6.
case H7: (tcd1 == tcd2); [move/eqP: H7=>?; subst tcd2| constructor 2];
  last by case=>?; subst tcd2;rewrite eqxx in H7.
case H8: (tpd1 == tpd2); [move/eqP: H8=>?; subst tpd2| constructor 2];
  last by case=>?; subst tpd2;rewrite eqxx in H8.
case H9: (dse1 == dse2); [move/eqP: H9=>?; subst dse2| constructor 2];
  last by case=>?; subst dse2;rewrite eqxx in H9.
case H10: (die1 == die2); [move/eqP: H10=>?; subst die2| constructor 2];
  last by case=>?; subst die2;rewrite eqxx in H10.
case H11: (vo1 == vo2); [move/eqP: H11=>?; subst vo2| constructor 2];
  last by case=>?; subst vo2;rewrite eqxx in H11.
case H12: (mh1 == mh2); [move/eqP: H12=>?; subst mh2| constructor 2];
  last by case=>?; subst mh2;rewrite eqxx in H12.
by constructor 1.
Qed.

Definition CasperData_eqMixin :=
  Eval hnf in EqMixin eq_CasperDataP.
Canonical CasperData_eqType :=
  Eval hnf in EqType CasperData CasperData_eqMixin.
