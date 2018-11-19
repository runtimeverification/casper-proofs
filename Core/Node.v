From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype div path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
  This module defines the data structures
  for the Beacon Chain protocol
 *)

Parameter byte : ordType.
Parameter Address : finType.

Inductive Sender :=
| NullSender : Sender
| AddrSender : Address -> Sender.

Definition eq_Sender (s s' : Sender) :=
  match s, s' with
  | NullSender, NullSender => true
  | NullSender, _ => false
  | AddrSender a1, AddrSender a2 => a1 == a2
  | AddrSender _, _ => false
  end.

Lemma eq_SenderP : Equality.axiom eq_Sender.
Proof.
case => [|a1]; case => [|a2].
- by constructor 1.
- by constructor 2.
- by constructor 2.
- rewrite /eq_Sender /=.
  case H1: (a1 == a2); [move/eqP: H1=>?; subst a2| constructor 2];
    last by case=>?; subst a2;rewrite eqxx in H1.
  by constructor 1.
Qed.

Definition Sender_eqMixin :=
  Eval hnf in EqMixin eq_SenderP.
Canonical Sender_eqType :=
  Eval hnf in EqType Sender Sender_eqMixin.

Record AttestationRecord {Hash : ordType} :=
  mkAR {
    slot_ar : nat;
    shard_id : nat;
    oblique_parent_hashes : seq Hash;
    shard_block_hash : Hash;
    attester_bitfield : seq byte;
    aggregate_sig : seq nat
  }.

Record Block {Hash : ordType} :=
  mkB {
    (* Hash of the parent block *)
    parent_hash : Hash;
    (* Slot number (for the PoS mechanism) *)
    slot_number : nat;
    (* Randao commitment reveal *)
    randao_reveal : Hash;
    (* Attestations *)
    attestations : seq (@AttestationRecord Hash);
    (* Reference to PoW chain block *)
    pow_chain_ref : Hash;
    (* Hash of the active state *)
    active_state_root : Hash;
    (* Hash of the crystallized state *)
    crystallized_state_root : Hash;
  }.

Record ShardAndCommittee :=
  mkSAC {
    (* The shard ID *)
    shard_id_sac : nat;
    (* Validator indices *)
    committee : seq nat
  }.

Record CrosslinkRecord {Hash : ordType} :=
  mkCR {
    (* What dynasty the crosslink was submitted in *)
    dynasty : nat;
    (* slot during which crosslink was added *)
    slot : nat;
    (* The block hash *)
    hash : Hash
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
    randao_commitment : Hash;
    (* Current balance *)
    balance : nat;
    (* Dynasty where the validator is inducted *)
    start_dynasty : nat;
    (* Dynasty where the validator leaves *)
    end_dynasty : nat
  }.

Record ActiveState {Hash : ordType} :=
  mkAS {
    (* Attestations that have not yet been processed *)
    pending_attestations : seq (@AttestationRecord Hash);
    (* Most recent 2*CYCLE_LENGTH block hashes, older to newer *)
    recent_block_hashes : seq Hash;
    (* TODO: need to have block_vote_cache and chain here? *)
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
    shard_and_committee_for_slots: seq (seq ShardAndCommittee);
    (* The last justified slot *)
    last_justified_slot: nat;
    (* Number of consecutive justified slots ending at this one *)
    justified_streak: nat;
    (* The last finalized slot *)
    last_finalized_slot: nat;
    (* The current dynasty *)
    current_dynasty: nat;
    (* Records about the most recent crosslink for each shard *)
    crosslink_records: seq (@CrosslinkRecord Hash);
    (* Used to select the committees for each shard *)
    dynasty_seed: Hash;
    (* Last epoch the crosslink seed was reset *)
    dynasty_start: nat;
  }.

Definition eq_validator_record {H : ordType} (vr vr' : @ValidatorRecord H) :=
  match vr, vr' with
  | mkVR pk ws wa rc b sd ed, mkVR pk' ws' wa' rc' b' sd' ed' =>
    [&& pk == pk', ws == ws', wa == wa', rc == rc', b == b', sd == sd' & ed == ed']
  end.

Lemma eq_validator_recordP {H : ordType} : Equality.axiom (@eq_validator_record H).
case=> pk ws wa rc b sd ed; case=> pk' ws' wa' rc' b' sd' ed'; rewrite /eq_validator_record/=.
case H2: (pk == pk'); [move/eqP: H2=>?; subst pk'| constructor 2];
  last by case=>?; subst pk';rewrite eqxx in H2.
case H3: (ws == ws'); [move/eqP: H3=>?; subst ws'| constructor 2];
  last by case=>?; subst ws';rewrite eqxx in H3.
case H4: (wa == wa'); [move/eqP: H4=>?; subst wa'| constructor 2];
  last by case=>?; subst wa';rewrite eqxx in H4.
case H5: (rc == rc'); [move/eqP: H5=>?; subst rc'| constructor 2];
  last by case=>?; subst rc';rewrite eqxx in H5.
case H6: (b == b'); [move/eqP: H6=>?; subst b'| constructor 2];
  last by case=>?; subst b';rewrite eqxx in H6.
case H7: (sd == sd'); [move/eqP: H7=>?; subst sd'| constructor 2];
  last by case=>?; subst sd';rewrite eqxx in H7.
case H8: (ed == ed'); [move/eqP: H8=>?; subst ed'| constructor 2];
  last by case=>?; subst ed';rewrite eqxx in H8.
by constructor 1.
Qed.

Canonical ValidatorRecord_eqMixin {H : ordType} :=
  Eval hnf in EqMixin (@eq_validator_recordP H).
Canonical ValidatorRecord_eqType {H : ordType} :=
  Eval hnf in EqType (@ValidatorRecord H) (@ValidatorRecord_eqMixin H).

Definition eq_attestation_record {H : ordType} (ar ar' : @AttestationRecord H) :=
  match ar, ar' with
  | mkAR sa si oph sbh ab ags, mkAR sa' si' oph' sbh' ab' ags' =>
    [&& sa == sa', si == si', oph == oph', sbh == sbh', ab == ab' & ags == ags']
  end.

Lemma eq_attestation_recordP {H : ordType} : Equality.axiom (@eq_attestation_record H).
Proof.
case=> sa si oph sbh ab ags; case=> sa' si' oph' sbh' ab' ags'; rewrite /eq_attestation_record/=.
case H2: (sa == sa'); [move/eqP: H2=>?; subst sa'| constructor 2];
  last by case=>?; subst sa';rewrite eqxx in H2.
case H3: (si == si'); [move/eqP: H3=>?; subst si'| constructor 2];
  last by case=>?; subst si';rewrite eqxx in H3.
case H4: (oph == oph'); [move/eqP: H4=>?; subst oph'| constructor 2];
  last by case=>?; subst oph';rewrite eqxx in H4.
case H5: (sbh == sbh'); [move/eqP: H5=>?; subst sbh'| constructor 2];
  last by case=>?; subst sbh';rewrite eqxx in H5.
case H6: (ab == ab'); [move/eqP: H6=>?; subst ab'| constructor 2];
  last by case=>?; subst ab';rewrite eqxx in H6.
case H7: (ags == ags'); [move/eqP: H7=>?; subst ags'| constructor 2];
  last by case=>?; subst ags';rewrite eqxx in H7.
by constructor 1.
Qed.

Canonical AttestationRecord_eqMixin {H : ordType} :=
  Eval hnf in EqMixin (@eq_attestation_recordP H).
Canonical AttestationRecord_eqType {H : ordType} :=
  Eval hnf in EqType (@AttestationRecord H) (@AttestationRecord_eqMixin H).

Definition eq_block {H : ordType} (b b' : @Block H) :=
  match b, b' with
  | mkB ph sn rr ars pcr asr csr, mkB ph' sn' rr' ars' pcr' asr' csr' =>
    [&& ph == ph', sn == sn', rr == rr', ars == ars', pcr == pcr', asr == asr' & csr == csr']
  end.
      
Lemma eq_blockP {H : ordType} : Equality.axiom (@eq_block H).
Proof.
case=> ph sn rr ars pcr asr csr;
case=> ph' sn' rr' ars' pcr' asr' csr'; rewrite /eq_block/=.
case H2: (ph == ph'); [move/eqP: H2=>?; subst ph'| constructor 2];
  last by case=>?; subst ph';rewrite eqxx in H2.
case H3: (sn == sn'); [move/eqP: H3=>?; subst sn'| constructor 2];
  last by case=>?; subst sn';rewrite eqxx in H3.
case H4: (rr == rr'); [move/eqP: H4=>?; subst rr'| constructor 2];
  last by case=>?; subst rr';rewrite eqxx in H4.
case H5: (ars == ars'); [move/eqP: H5=>?; subst ars'| constructor 2];
  last by case=>?; subst ars';rewrite eqxx in H5.
case H6: (pcr == pcr'); [move/eqP: H6=>?; subst pcr'| constructor 2];
  last by case=>?; subst pcr';rewrite eqxx in H6.
case H7: (asr == asr'); [move/eqP: H7=>?; subst asr'| constructor 2];
  last by case=>?; subst asr';rewrite eqxx in H7.
case H8: (csr == csr'); [move/eqP: H8=>?; subst csr'| constructor 2];
  last by case=>?; subst csr';rewrite eqxx in H8.
by constructor 1. 
Qed.

Canonical Block_eqMixin {H : ordType} :=
  Eval hnf in EqMixin (@eq_blockP H ).
Canonical Block_eqType {H : ordType} :=
  Eval hnf in EqType (@Block H) (@Block_eqMixin H).

Parameter Hash : finType.
Parameter NodeId : finType.
Parameter Timestamp : Type.

Definition Hash_ordMixin := fin_ordMixin Hash.
Canonical Hash_finType := Eval hnf in OrdType Hash Hash_ordMixin.

Definition block := @Block [ordType of Hash].

Parameter GenesisBlock : block.

Definition Blockforest := union_map [ordType of Hash] block.

Parameter hashB : block -> Hash.

Axiom hashB_inj : injective hashB.

Notation "# b" := (hashB b) (at level 20).

Definition get_block (bf : Blockforest) k : Block :=
  if find k bf is Some b then b else GenesisBlock.

Definition has_init_block (bf : Blockforest) :=
  find (# GenesisBlock) bf = Some GenesisBlock.

Definition bfExtend (bf : Blockforest) (b : block) :=
  if #b \in dom bf then bf else #b \\-> b \+ bf.

Definition validH (bf : Blockforest) :=
  forall h b, find h bf = Some b -> h = hashB b.

Lemma bfExtendV bf b : valid bf = valid (bfExtend bf b).
Proof.
rewrite /bfExtend; case: ifP=>//N.
by rewrite validPtUn/= N andbC.
Qed.

Lemma bfExtendH bf b : valid bf -> validH bf -> validH (bfExtend bf b).
Proof.
move=>V H z c; rewrite /bfExtend.
case: ifP=>X; first by move/H.
rewrite findUnL ?validPtUn ?V ?X//.
case: ifP=>Y; last by move/H.
rewrite domPt inE in Y; move/eqP: Y=>Y; subst z.
by rewrite findPt; case=>->.
Qed.

Lemma bfExtendIB bf b :
  valid bf -> validH bf -> has_init_block bf ->
  has_init_block (bfExtend bf b).
Proof.
move=>V H; rewrite /bfExtend/has_init_block=>Ib.
case: ifP=>X; first done.
rewrite findUnL ?validPtUn ?V ?X//.
case: ifP=>Y; last done.
rewrite domPt inE in Y; move/eqP: Y=>Y.
by specialize (hashB_inj Y)=><-; rewrite Y findPt.
Qed.

(* HELPERS *)

Definition set_crystallized_state_validators a v := @mkCS [ordType of Hash] v (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_last_state_recalc a v := @mkCS [ordType of Hash] (validators a) v (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_shard_and_committee_for_slots a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) v (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_last_justified_slot a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) v (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_justified_streak a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) v (last_finalized_slot a) (current_dynasty a) (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_last_finalized_slot a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) v (current_dynasty a) (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_current_dynasty a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) v (crosslink_records a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_crosslink_records a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) v (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_dynasty_seed a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslink_records a) v (dynasty_start a).
Definition set_crystallized_state_dynasty_start a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslink_records a) (dynasty_seed a) v.

Notation "{[ a 'with' 'validators' := v ]}" := (set_crystallized_state_validators a v).
Notation "{[ a 'with' 'last_state_recalc' := v ]}" := (set_crystallized_state_last_state_recalc a v).
Notation "{[ a 'with' 'shard_and_committee_for_slots' := v ]}" := (set_crystallized_state_shard_and_committee_for_slots a v).
Notation "{[ a 'with' 'last_justified_slot' := v ]}" := (set_crystallized_state_last_justified_slot a v).
Notation "{[ a 'with' 'justified_streak' := v ]}" := (set_crystallized_state_justified_streak a v).
Notation "{[ a 'with' 'last_finalized_slot' := v ]}" := (set_crystallized_state_last_finalized_slot a v).
Notation "{[ a 'with' 'current_dynasty' := v ]}" := (set_crystallized_state_current_dynasty a v).
Notation "{[ a 'with' 'crosslink_records' := v ]}" := (set_crystallized_state_crosslink_records a v).
Notation "{[ a 'with' 'dynasty_seed' := v ]}" := (set_crystallized_state_dynasty_seed a v).
Notation "{[ a 'with' 'dynasty_start' := v ]}" := (set_crystallized_state_dynasty_start a v).

Arguments set_crystallized_state_validators  _ _/.
Arguments set_crystallized_state_last_state_recalc  _ _/.
Arguments set_crystallized_state_shard_and_committee_for_slots  _ _/.
Arguments set_crystallized_state_last_justified_slot  _ _/.
Arguments set_crystallized_state_justified_streak  _ _/.
Arguments set_crystallized_state_last_finalized_slot  _ _/.
Arguments set_crystallized_state_current_dynasty  _ _/.
Arguments set_crystallized_state_crosslink_records  _ _/.
Arguments set_crystallized_state_dynasty_seed  _ _/.
Arguments set_crystallized_state_dynasty_start  _ _/.

Definition set_validator_record_pubkey a v := @mkVR [ordType of Hash] v (withdrawal_shard a) (withdrawal_address a) (randao_commitment a) (balance a) (start_dynasty a) (end_dynasty a).
Definition set_validator_record_withdrawal_shard a v := @mkVR [ordType of Hash] (pubkey a) v (withdrawal_address a) (randao_commitment a) (balance a) (start_dynasty a) (end_dynasty a).
Definition set_validator_record_withdrawal_address a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) v (randao_commitment a) (balance a) (start_dynasty a) (end_dynasty a).
Definition set_validator_record_randao_commitment a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) (withdrawal_address a) v (balance a) (start_dynasty a) (@end_dynasty [ordType of Hash] a).
Definition set_validator_record_balance a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) (withdrawal_address a) (randao_commitment a) v (start_dynasty a) (end_dynasty a).
Definition set_validator_record_start_dynasty a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) (withdrawal_address a) (randao_commitment a) (balance a) v (end_dynasty a).
Definition set_validator_record_end_dynasty a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) (withdrawal_address a) (randao_commitment a) (balance a) (start_dynasty a) v.

Notation "{[ a 'with' 'pubkey' := v ]}" := (set_validator_record_pubkey a v).
Notation "{[ a 'with' 'withdrawal_shard' := v ]}" := (set_validator_record_withdrawal_shard a v).
Notation "{[ a 'with' 'withdrawal_address' := v ]}" := (set_validator_record_withdrawal_address a v).
Notation "{[ a 'with' 'balance' := v ]}" := (set_validator_record_balance a v).
Notation "{[ a 'with' 'start_dynasty' := v ]}" := (set_validator_record_start_dynasty a v).
Notation "{[ a 'with' 'end_dynasty' := v ]}" := (set_validator_record_end_dynasty a v).

Arguments set_validator_record_pubkey  _ _/.
Arguments set_validator_record_withdrawal_shard  _ _/.
Arguments set_validator_record_withdrawal_address  _ _/.
Arguments set_validator_record_balance  _ _/.
Arguments set_validator_record_start_dynasty  _ _/.
Arguments set_validator_record_end_dynasty  _ _/.

Definition NodeId_ordMixin := fin_ordMixin NodeId.
Canonical NodeId_ordType := Eval hnf in OrdType NodeId NodeId_ordMixin.

(* Parameters *)
Parameter dummyHash : Hash.
Parameter dummySAC : ShardAndCommittee.
Parameter dummySACSeq : seq ShardAndCommittee.
Parameter dummyCR : @CrosslinkRecord [ordType of Hash].
Parameter dummyVal : @ValidatorRecord [ordType of Hash].

Parameter BlockVoteCache : Type.

(* -------------------- *)
(* NEW CASPER FUNCTIONS *)
(* -------------------- *)

(* helper functions - see helper.py *)

Definition getShardsAndCommitteesForSlot (crystallizedState : @CrystallizedState [ordType of Hash])
           (slot : nat)
           (cycleLength : nat) : seq ShardAndCommittee :=
  let: start := (last_state_recalc crystallizedState) - cycleLength in
  if (slot < start) || (start + cycleLength * 2 <= slot) then (* TODO: throw exception *) [::] else
    nth dummySACSeq (shard_and_committee_for_slots crystallizedState) (slot - start).

Definition getAttestationIndices (crystallizedState : @CrystallizedState [ordType of Hash])
           (attestation : @AttestationRecord [ordType of Hash])
           (cycleLength : nat) : seq nat :=
  let: attSlot := slot_ar attestation in
  let: SACForSlot := getShardsAndCommitteesForSlot crystallizedState attSlot cycleLength in
  let: shardId := shard_id attestation in
  let: filteredSACForSlot := filter (fun x => shard_id_sac x == shardId) SACForSlot in
  let: shardAndCommittee := ohead filteredSACForSlot in
  match shardAndCommittee with
    | None => [::]
    | Some sac => committee sac
  end.

(* TODO: implement *)
Definition getNewShuffling (seed : Hash)
           (validators : seq (@ValidatorRecord [ordType of Hash]))
           (dynasty : nat) (crosslinkingStartShard : nat) : seq (seq ShardAndCommittee) :=
  [::].

Definition getNewRecentBlockHashes (oldBlockHashes : seq Hash) (parentSlot : nat)
           (currentSlot : nat) (parentHash : Hash) : seq Hash :=
  let: d := currentSlot - parentSlot in
  drop d oldBlockHashes ++ nseq (min d (size oldBlockHashes)) parentHash.

(* Return validators who are currently participating *)
Definition getActiveValidatorIndices (dynasty : nat)
           (validators : seq (@ValidatorRecord [ordType of Hash])) : seq nat :=
  let: indices := iota 0 (size validators) in
  let: filteredValidators := map (fun x => (start_dynasty x <= dynasty) && (dynasty < end_dynasty x)) validators in
  filter (fun x => nth false filteredValidators x == true) indices.

(* helper function - see CrystallizedState.py *)

(* Calculate total deposits of all active validators in a crystallized state *)
Definition totalDeposits (crystallizedState : @CrystallizedState [ordType of Hash]) : nat :=
  let: vals := validators crystallizedState in
  let: currentDynasty := current_dynasty crystallizedState in
  let: balances := map (fun x => balance (nth dummyVal vals x))
                       (getActiveValidatorIndices currentDynasty vals) in
  sumn balances.

(* helper functions - see bitfield.py *)

Definition getBitfieldLength (bitCount : nat) : nat :=
  (bitCount + 7) %/ 8.

(* TODO: implement *)
Definition checkLastBits (attBitfield : seq byte) (lastBit : nat) : bool := true.

(* state transition functions - see state_transition.py *)

(* Return reward context: tuple of reward quotient, quadratic penalty quotient *)
(* TODO: implement *)
Definition getRewardContext (totalDeposits : nat) : nat * nat :=
  if totalDeposits <= 0 then (* TODO: throw exception *) (0, 0) else
    (0, 0).

(* Validate slot number, justified slot and justified block hash *)
Definition validateAttestation (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (attestation : @AttestationRecord [ordType of Hash])
           (blk : block)
           (cycleLength : nat) : bool :=
  if slot_number blk <= slot_ar attestation then (* TODO: throw exception *) false
  else
    let: attestationIndices := getAttestationIndices crystallizedState attestation cycleLength in
    let: lastBit := size attestationIndices in
    let: attBitfield := attester_bitfield attestation in
    if size attBitfield != getBitfieldLength lastBit then (* TODO: throw exception *) false
    else
      if lastBit %% 8 == 0 then checkLastBits attBitfield lastBit
      else (* TODO: create pubKeys, message, call verify *) true.

(* TODO: implement *)
Definition getUpdatedBlockVoteCache (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (attestation : @AttestationRecord [ordType of Hash])
           (blk : block)
           (blkVoteCache : BlockVoteCache) : BlockVoteCache :=
  blkVoteCache.

(* Process block, return new active state *)
Definition processBlock (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) : ActiveState :=
  if all (fun x => validateAttestation crystallizedState activeState x blk cycleLength) (attestations blk) then
    (* TODO: throw exception *) activeState
  else
    (* TODO: new block vote cache *)
    let: newAtts := pending_attestations activeState ++ attestations blk in
    let: recentBlockHashes := recent_block_hashes activeState in
    (* TODO: new chain *)
    (* TODO: update activeState with newBlockVoteCache, chain *)
    @mkAS [ordType of Hash] newAtts recentBlockHashes.

(* Process crosslinks from crystallized state *)
Definition processUpdatedCrosslinks (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block) (cycleLength : nat) : seq (@CrosslinkRecord [ordType of Hash]) :=
  let: totalAttestationBalance := Nil ((nat * Hash) * nat) in
  let: crosslinks := crosslink_records crystallizedState in
  let: pendingAtts := pending_attestations activeState in
  let: (newAttBalance, newCrosslinks) :=
     foldr
       (fun i acc =>
          let: shardTuple := (shard_id i, shard_block_hash i) in
          let: acc'0 :=
             if shardTuple \notin (map fst (fst acc)) then
               cons (shardTuple, 0) (fst acc) else
               fst acc in
          let: attIndices := getAttestationIndices crystallizedState i cycleLength in
          let: totalCommitteeBalance :=
             foldr (fun j ps => balance (nth dummyVal (validators crystallizedState) j) + ps) 0 attIndices in
          (* TODO: finish implementing: if 2/3 of committee voted on crosslink and do not
             yet have crosslink for this shard, for this dynasty, add updated crosslink *)
       (acc'0, snd acc))
       (totalAttestationBalance, crosslinks)
       pendingAtts in
  crosslinks.

(* Balance recalculations related to ffg rewards *)
Definition calculateFfgRewards (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) : seq nat :=
  let: validators := validators crystallizedState in
  let: activeValidatorIndices := getActiveValidatorIndices (current_dynasty crystallizedState) validators in
  let: rewardsAndPenalties := map (fun _ => 0) validators in
  let: timeSinceFinality := slot_number blk - last_finalized_slot crystallizedState in
  let: totalDeposits := totalDeposits crystallizedState in
  let: (rewardQuotient, quadraticPenaltyQuotient) := getRewardContext totalDeposits in
  let: lastStateRecalc := last_state_recalc crystallizedState in
  let: loopList := iota (lastStateRecalc - cycleLength) cycleLength in
  let: newRewardsAndPenalties :=
     foldr
       (fun i acc =>
          (* TODO: blockVoteCache, chain parameter in activeState *)
          let: totalParticipatedDeposits := 0 in
          let: voterIndices := [::] in
          let: participatingValidatorIndices :=
             filter (fun x => x \in voterIndices) activeValidatorIndices in
          let: nonParticipatingValidatorIndices :=
             filter (fun x => x \notin voterIndices) activeValidatorIndices in
          map
            (fun ind =>
               let: curr := nth 0 rewardsAndPenalties ind in
               let: valBal := balance (nth dummyVal validators ind) in
               if timeSinceFinality <= 3 * cycleLength then
                 if ind \in participatingValidatorIndices then
                   curr + valBal %/ rewardQuotient * (2 * totalParticipatedDeposits - totalDeposits) %/ totalDeposits else
                   curr - valBal %/ rewardQuotient
               else
                 curr - (valBal %/ rewardQuotient) + (valBal * timeSinceFinality %/ rewardQuotient))
            acc)
       rewardsAndPenalties
       loopList in
  newRewardsAndPenalties.

(* Balance recalculations related to crosslink rewards *)
(* TODO: implement *)
Definition calculateCrosslinkRewards (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block) : seq nat :=
  let: validators := validators crystallizedState in
  map (fun _ => 0) validators.

(* Apply rewards and penalties for all validators in crystallized state *)
Definition applyRewardsAndPenalties (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) : seq (@ValidatorRecord [ordType of Hash]) :=
  let: validators := validators crystallizedState in
  let: ffgRewards := calculateFfgRewards crystallizedState activeState blk cycleLength in
  let: crosslinkRewards := calculateCrosslinkRewards crystallizedState activeState blk in
  let: activeValidatorIndices := getActiveValidatorIndices (current_dynasty crystallizedState) validators in
  map
    (fun x =>
       let: ind := index x validators in
       if ind \in activeValidatorIndices
       then {[ x with balance :=
                 max 0 (balance x + nth 0 ffgRewards ind + nth 0 crosslinkRewards ind) ]}
       else id x)
    validators.

(* Initialize new cycle: cycle corresponds to a span of slots during which all validators
   get exactly one chance to make an attestation *)
Definition initializeNewCycle (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) : CrystallizedState * ActiveState :=
  let: lastStateRecalc := last_state_recalc crystallizedState in
  let: lastJustifiedSlot := last_justified_slot crystallizedState in
  let: lastFinalizedSlot := last_finalized_slot crystallizedState in
  let: justifiedStreak := justified_streak crystallizedState in
  let: totalDeposits := totalDeposits crystallizedState in
  let: recentBlockHashes := recent_block_hashes activeState in
  let: cycleLengthList := iota 0 cycleLength in
  let: (lastJustifiedSlot', (justifiedStreak', lastFinalizedSlot')) :=
     foldr
       (fun i acc =>
          let: slot := i + (lastStateRecalc - cycleLength) in
          let: blockHash := nth dummyHash recentBlockHashes i in
          (* TODO: block vote cache *)
          let: voteBalance := 0 in
          let: (acc'1, acc'2) := if 2 * totalDeposits <= 3 * voteBalance then
                                   (max (fst acc) slot, (fst (snd acc)) + 1) else (0, 0) in
          if cycleLength + 1 <= acc'1 then
            (acc'1, (acc'2, max (snd (snd acc)) (slot - cycleLength - 1)))
          else
            (acc'1, (acc'2, snd (snd acc))))
       (lastJustifiedSlot, (justifiedStreak, lastFinalizedSlot))
       cycleLengthList in
  let: crosslinkRecords := processUpdatedCrosslinks crystallizedState activeState blk cycleLength in
  let: pendingAtts := pending_attestations activeState in
  let: newPendingAtts := filter (fun a => lastStateRecalc <= slot_ar a) pendingAtts in
  let: validators := applyRewardsAndPenalties crystallizedState activeState blk cycleLength in
  let: SACForSlots := shard_and_committee_for_slots crystallizedState in
  let: newSACForSlots := drop cycleLength SACForSlots ++ drop cycleLength SACForSlots in
  let: crystallizedState'0 := {[ crystallizedState with validators := validators ]} in
  let: crystallizedState'1 := {[ crystallizedState'0 with last_state_recalc := lastStateRecalc + cycleLength ]} in
  let: crystallizedState'2 := {[ crystallizedState'1 with last_justified_slot := lastJustifiedSlot' ]} in
  let: crystallizedState'3 := {[ crystallizedState'2 with justified_streak := justifiedStreak' ]} in
  let: crystallizedState'4 := {[ crystallizedState'3 with last_finalized_slot := lastFinalizedSlot' ]} in
  let: crystallizedState'5 := {[ crystallizedState'4 with crosslink_records := crosslinkRecords ]} in
  let: activeState' := @mkAS [ordType of Hash] newPendingAtts recentBlockHashes in
  (crystallizedState'5, activeState').

Definition fillRecentBlockHashes (activeState : @ActiveState [ordType of Hash])
           (parentBlk : block)
           (blk : block) : ActiveState :=
  let: pendingAtts := pending_attestations activeState in
  let: newRecentBlockHashes := getNewRecentBlockHashes
                                 (recent_block_hashes activeState)
                                 (slot_number parentBlk)
                                 (slot_number blk)
                                 (parent_hash blk) in
  (* TODO: update activeState with newBlockVoteCache, chain *)
  @mkAS [ordType of Hash] pendingAtts newRecentBlockHashes.

(* Check if crystallized state should transition to next dynasty *)
Definition readyForDynastyTransition (crystallizedState : @CrystallizedState [ordType of Hash])
           (blk : block)
           (minDynastyLength : nat) : bool :=
  let: dynastyStart := dynasty_start crystallizedState in
  let: slotsSinceLastDynastyChange := (slot_number blk) - dynastyStart in
  if slotsSinceLastDynastyChange < minDynastyLength then false else
    if (last_finalized_slot crystallizedState) <= dynastyStart then false else
      let: flatSACForSlots := flatten (shard_and_committee_for_slots crystallizedState) in
      let: requiredShards := undup (map shard_id_sac flatSACForSlots) in
      let: crosslinkRecords := crosslink_records crystallizedState in
      let: indices := iota 0 (size crosslinkRecords) in
      let: newList := filter (fun x => x \in requiredShards) indices in
      all (fun x => dynastyStart < slot (nth dummyCR crosslinkRecords x)) indices.

(* State transition corresponding to new dynasty *)
Definition computeDynastyTransition (crystallizedState : @CrystallizedState [ordType of Hash])
           (blk : block)
           (shardCount : nat)
           (cycleLength : nat) : CrystallizedState :=
  let: newDynasty := current_dynasty crystallizedState + 1 in
  let: lastShardSeq := last [::] (shard_and_committee_for_slots crystallizedState) in
  let: nextShard := last dummySAC lastShardSeq in
  let: nextStartShard := shard_id_sac nextShard %/ shardCount in
  let: validators := validators crystallizedState in
  let: newShuffling := getNewShuffling (parent_hash blk) validators newDynasty nextStartShard in
  let: subSACForSlots := take cycleLength (shard_and_committee_for_slots crystallizedState) in
  let: newSACForSlots := subSACForSlots ++ newShuffling in
  let: crystallizedState'0 := {[ crystallizedState with validators := validators ]} in
  let: crystallizedState'1 := {[ crystallizedState with shard_and_committee_for_slots := newSACForSlots ]} in
  let: crystallizedState'2 := {[ crystallizedState with current_dynasty := newDynasty ]} in
  crystallizedState'2.

(* TODO: should emulate while loop ideally instead of initializing cycle once *)
Definition computeCycleTransitions (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (shardCount : nat)
           (cycleLength : nat) : CrystallizedState * ActiveState :=
  if slot_number blk < (last_state_recalc crystallizedState + cycleLength) then
    let: (crystallizedState'0, activeState') :=
       initializeNewCycle crystallizedState activeState blk cycleLength in
    if readyForDynastyTransition crystallizedState blk cycleLength then
      let crystallizedState'1 :=
          computeDynastyTransition crystallizedState blk shardCount cycleLength in
      (crystallizedState'1, activeState')
    else (crystallizedState'0, activeState')
  else (crystallizedState, activeState).

(* State transition function: update crystallized and active states *)
Definition computeStateTransition (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (parentBlk : block)
           (blk : block)
           (shardCount : nat)
           (cycleLength : nat) : CrystallizedState * ActiveState :=
  let: activeState'0 := fillRecentBlockHashes activeState parentBlk blk in
  let: activeState'1 := processBlock crystallizedState activeState blk in
  computeCycleTransitions crystallizedState activeState blk shardCount cycleLength.

(* ------------------*)
(* PROTOCOL MESSAGES *)
(* ------------------*)

Definition peers_t := seq NodeId.

Inductive Message :=
| BlockMsg of block.

Inductive InternalTransition :=
  | BlockT of block.

Definition eq_msg a b :=
 match a, b with
  | BlockMsg bA, BlockMsg bB => (bA == bB)
 end.

Ltac simple_tactic mb n n' B :=
  (case: mb=>//b'; do? [by constructor 2];
   case B: (n == n'); [by case/eqP:B=><-; constructor 1|constructor 2];
   case=>E; subst n'; rewrite eqxx in B).

Lemma eq_msgP : Equality.axiom eq_msg.
Proof.
move=> ma mb. rewrite/eq_msg.
case: ma=>b.
case:mb=>////b'; do? [by constructor 2].
case B: (b == b'); [by case/eqP:B=><-; constructor 1|constructor 2].
by case=>Z; subst b'; rewrite eqxx in B.
Qed.
  
Canonical Msg_eqMixin := Eval hnf in EqMixin eq_msgP.
Canonical Msg_eqType := Eval hnf in EqType Message Msg_eqMixin.

Record Packet := mkP {src: NodeId; dst: NodeId; msg: Message}.

Definition eq_pkt a b :=
  ((src a) == (src b)) && ((dst a) == (dst b)) && ((msg a) == (msg b)).

Lemma eq_pktP : Equality.axiom eq_pkt.
Proof.
case=>sa da ma [sb] db mb; rewrite/eq_pkt/=.
case P1: (sa == sb)=>/=; last by constructor 2; case=>/eqP; rewrite P1.
case P2: (da == db)=>/=; last by constructor 2; case=> _ /eqP; rewrite P2.
case P3: (ma == mb)=>/=; last by constructor 2; case=> _ _ /eqP; rewrite P3.
by constructor 1; move/eqP: P1=><-; move/eqP: P2=><-; move/eqP: P3=><-.
Qed.

Canonical Packet_eqMixin := Eval hnf in EqMixin eq_pktP.
Canonical Packet_eqType := Eval hnf in EqType Packet Packet_eqMixin.

Definition ToSend := seq Packet.
Definition emitZero : ToSend := [::].
Definition emitOne (packet : Packet) : ToSend := [:: packet].
Definition emitMany (packets : ToSend) := packets.

Definition emitBroadcast (from : NodeId) (dst : seq NodeId) (msg : Message) :=
  [seq (mkP from to msg) | to <- dst].

(* ------------------*)
(* NODE STATE & CODE *)
(* ------------------*)

Record State {Hash : ordType} :=
  Node {
    id : NodeId;
    peers : peers_t;
    blocks : Blockforest;
    cstate : @CrystallizedState Hash;
    astate : @ActiveState Hash;
    (* TODO: do shardCount, cycleLength belong here? *)
    shardCount : nat;
    cycleLength : nat;
  }.

(* Initial values defined in beacon chain repo *)
Definition initCS := @mkCS [ordType of Hash] [::] 0 [::] 0 0 0 0 [::] dummyHash 0.
Definition initAS := @mkAS [ordType of Hash] [::] [::].

(* Initial values for crystallized state, active state, shardCount, and cycleLength
   are defined in the beacon chain repo. *)
Definition Init (n : NodeId) (peers : seq NodeId) : State :=
  Node n peers (#GenesisBlock \\-> GenesisBlock) initCS initAS 1024 64.

Definition procMsg (st: @State [ordType of Hash]) (from : NodeId) (msg: Message) (ts: Timestamp) :=
  let: Node n prs bf cst ast sc cl := st in
  match msg with
  | BlockMsg b =>
    let: parentBlock := get_block bf (parent_hash b) in
    let: (crystallizedState, activeState) := computeStateTransition cst ast parentBlock b sc cl in
    let: newBf := bfExtend bf b in
    pair (Node n prs newBf crystallizedState activeState sc cl) emitZero
  end.

Definition procInt (st : @State [ordType of Hash]) (tr : InternalTransition) (ts : Timestamp) :=
 let: Node n prs bf cst ast sc cl := st in
 match tr with
 | BlockT b =>
   let: parentBlock := get_block bf (parent_hash b) in
   let: (crystallizedState, activeState) := computeStateTransition cst ast parentBlock b sc cl in
   let: newBf := bfExtend bf b in
   pair (Node n prs newBf crystallizedState activeState sc cl) (emitBroadcast n prs (BlockMsg b))
 end.
