From mathcomp
Require Import all_ssreflect.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import CasperOneMessage ValidatorQuorum Blockforest.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ValBlock.

Variable Validator : finType.

Definition genesis : Hash := #GenesisBlock.

Definition sState : Type := State Validator Hash.

Definition validator_safety :=
  @safety Validator Hash
   (top_validators Validator)
   (bot_validators Validator)
   (@bot_top_validator_intersection Validator).

Definition hash_parent_bf (bf : Blockforest) : rel Hash :=
  [rel x y | [&& y != #GenesisBlock,
   x \in dom bf, y \in dom bf &
   if find y bf is Some b then parent_hash b == x else false] ].

Lemma hash_parent_bf_eq :
  forall bf, valid bf -> validH bf ->
  forall h1 h2 h3 : Hash, hash_parent_bf bf h2 h1 -> hash_parent_bf bf h3 h1 -> h2 = h3.
Proof.
move => bf Hv Hvh h1 h2 h3.
rewrite /hash_parent_bf /= => Hh1 Hh2.
Admitted.

End ValBlock.

(*
(hash_parent : rel Hash) (genesis : Hash),
(forall h1 h2 : Hash, hash_parent h1 h2 -> h1 <> h2) ->
(forall h1 h2 h3 : Hash, hash_parent h2 h1 -> hash_parent h3 h1 -> h2 = h3) ->
*)
