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

Parameter byte : Type.

(* TODO: different sized integers? *)
(* Default m16? *)

(* TODO: need to figure out which records need equality types *)

Record AttestationRecord {Hash : ordType} :=
  mkAR {
    slot_ar: nat;
    shard_id_ar: nat;
    oblique_parent_hashes: seq Hash;
    shard_block_hash_ar: Hash;
    attester_bitfield: seq byte;
    aggregate_sig: seq nat
  }.

Record Block {Hash : ordType} :=
  mkB {
    (* Hash of the parent block *)
    parent_hash: Hash;
    (* Slot number (for the PoS mechanism) *)
    slot_number: nat;
    (* Randao commitment reveal *)
    randao_reveal: Hash;
    (* Attestations *)
    attestations: seq (@AttestationRecord Hash);
    (* Reference to PoW chain block *)
    pow_chain_ref: Hash;
    (* Hash of the active state *)
    active_state_root: Hash;
    (* Hash of the crystallized state *)
    crystallized_state_root: Hash
  }.

Record ActiveState {Hash : ordType} :=
  mkAS {
    (* Attestations that have not yet been processed *)
    pending_attestations : seq (@AttestationRecord Hash);
    (* Most recent 2*CYCLE_LENGTH block hashes, older to newer *)  
    recent_block_hashes : seq Hash
  }.

Record RecentProposerRecord {Hash : ordType} :=
  mkRPR {
    (* Proposer index *)
    index: nat;
    (* New RANDAO commitment *)
    randao_commitment_rpr: Hash;
    (* Balance delta *)
    balance_delta: nat
  }.

Record CrosslinkRecord {Hash : ordType} :=
  mkCR {
    (* What dynasty the crosslink was submitted in *)
    dynasty: nat;
    (* slot during which crosslink was added *)
    slot_cr: nat;
    (* The block hash *)
    hash: Hash
  }.

Record PartialCrosslinkRecord {Hash : ordType} :=
  mkPCR {
    (* What shard is the crosslink being made for *)
    shard_id_pcr: nat;
    (* Hash of the block *)
    shard_block_hash_pcr: Hash;
    (* Which of the eligible voters are voting for it (as a bitfield) *)
    voter_bitfield: seq byte
  }.

Record ShardAndCommittee :=
  mkSAC {
    (* The shard ID *)
    shard_id_sac: nat;
    (* Validator indices *)
    committee: seq nat
  }.

Record ValidatorRecord {Hash : ordType} :=
  mkVR {
    (* The validator's public key *)
    pubkey : nat;
    (* What shard the validators balance will be sent to after withdrawal *)
    withdrawal_shard : nat;
    (* And what address *)
    withdrawal_address : Sender;
    (* The validators current RANDAO beacon commitment *)
    randao_commitment_vr : Hash;
    (* Current balance *)
    balance : nat;
    (* Dynasty where the validator is inducted *)
    start_dynasty : nat;
    (* Dynasty where the validator leaves *)
    end_dynasty : nat
  }.

Record CrystallizedState {Hash : ordType} :=
  mkCS {
    (* List of validators *)
    validators: seq (@ValidatorRecord Hash);
    (* Last CrystallizedState recalculation *)
    last_state_recalc: nat;
    (* What active validators are part of the attester set *)
    (* at what height; and in what shard. Starts at slot *)
    (* last_state_recalc - CYCLE_LENGTH *)
    indices_for_slots: seq (seq ShardAndCommittee);
    (* The last justified slot *)
    last_justified_slot: nat;
    (* Number of consecutive justified slots ending at this one *)
    justified_streak: nat;
    (* The last finalized slot *)
    last_finalized_slot: nat;
    (* The current dynasty *)
    current_dynasty: nat;
    (* The next shard that crosslinking assignment will start from *)
    crosslinking_start_shard: nat;
    (* Records about the most recent crosslink for each shard *)
    crosslink_records: seq (@CrosslinkRecord Hash);
    (* Total balance of deposits *)
    total_deposits: nat;
    (* Used to select the committees for each shard *)
    dynasty_seed: Hash;
    (* Last epoch the crosslink seed was reset *)
    dynasty_seed_last_reset: nat;
  }.
