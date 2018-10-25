From mathcomp
Require Import all_ssreflect.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import CasperOneMessage ValidatorQuorum ValidatorDepositQuorum Blockforest.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ValBlock.

Variable Validator : finType.

Variable deposit : Validator -> nat.

Variable bf : Blockforest.

Definition hash_parent_bf : rel Hash :=
 [rel x y | [&& x \in dom bf, y \in dom bf &
  if find y bf is Some b then parent_hash b == x else false] ].

Lemma hash_parent_bf_eq :
  forall h1 h2 h3 : Hash, hash_parent_bf h2 h1 -> hash_parent_bf h3 h1 -> h2 = h3.
Proof.
move => h1 h2 h3.
move/and3P; case => H1 H2 Hf.
move/and3P; case => H'1 H'2 H'f.
move: Hf H'f.
case: (find _ _) => //.
by move => b; move/eqP =>-> /eqP.
Qed.

Lemma accountable_safety_bf_card :
  forall s : State Validator Hash,
    finalization_fork (top_validators Validator) hash_parent_bf (# GenesisBlock) s ->
    misbehaving_slashed (bot_validators Validator) s.
Proof.
apply: accountable_safety.
- exact: bot_top_validator_intersection.
- exact: hash_parent_bf_eq.
Qed.

Lemma accountable_safety_bf_deposit :
  forall s : State Validator Hash,
    finalization_fork (deposit_top_validators deposit) hash_parent_bf (# GenesisBlock) s ->
    misbehaving_slashed (deposit_bot_validators deposit) s.
Proof.
apply: accountable_safety.
- exact: deposit_bot_top_validator_intersection.
- exact: hash_parent_bf_eq.
Qed.

End ValBlock.
