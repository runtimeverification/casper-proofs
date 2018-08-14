From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype finset path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
Set Implicit Arguments.
From CasperToychain
Require Import Blockforest.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- *)
(* STATE *)
(* ----- *)

(* TODO: are integers ordType? *)
(* TODO: different sized integers? *)
(* TODO: "bytes" type? *)
Record AttestationRecord {Hash : ordType} :=
  mkAR {
    slot : ordType;
    shard_id : ordType;
    oblique_parent_hashes: seq Hash;
    shard_block_hash: Hash;
    attester_bitfield: ordType;
    aggregate_sig: seq ordType
  }.

Record ActiveState {Hash : ordType} :=
  mkAS {
    (* Attestations that have not yet been processed *)
    pending_attestations : seq (@AttestationRecord Hash);
    (* Most recent 2*CYCLE_LENGTH block hashes, older to newer *)  
    recent_block_hashes : seq Hash
  }.

Record ValidatorRecord {Hash : ordType} :=
  mkVR {
    (* The validator's public key *)
    pubkey : ordType;
    (* What shard the validators balance will be sent to after withdrawal *)
    withdrawal_shard : ordType;
    (* And what address *)
    withdrawal_address : Sender;
    (* The validators current RANDAO beacon commitment *)
    randao_commitment : Hash;
    (* Current balance *)
    balance : ordType;
    (* Dynasty where the validator is inducted *)
    start_dynasty : ordType;
    (* Dynasty where the validator leaves *)
    end_dynasty : ordType
  }.
