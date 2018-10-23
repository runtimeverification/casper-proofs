From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype div path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import Blockforest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
           (cycleLength : nat) (* TODO: config paramter? *) : seq ShardAndCommittee :=
  let: start := (last_state_recalc crystallizedState) - cycleLength in
  if (slot < start) || (start + cycleLength * 2 <= slot) then (* TODO: throw exception *) [::] else
    nth dummySACSeq (shard_and_committee_for_slots crystallizedState) (slot - start).

Definition getAttestationIndices (crystallizedState : @CrystallizedState [ordType of Hash])
           (attestation : @AttestationRecord [ordType of Hash])
           (cycleLength : nat) (* TODO: config paramter? *) : seq nat :=
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
  (* TODO: config parameter? *)
  [::].

Definition getNewRecentBlockHashes (oldBlockHashes : seq Hash) (parentSlot : nat)
           (currentSlot : nat) (parentHash : Hash) : seq Hash :=
  let: d := currentSlot - parentSlot in
  drop d oldBlockHashes ++ nseq (min d (size oldBlockHashes)) parentHash.

Definition getActiveValidatorIndices (dynasty : nat)
           (validators : seq (@ValidatorRecord [ordType of Hash])) : seq nat :=
  let: indices := iota 0 (size validators) in
  let: filteredValidators := map (fun x => (start_dynasty x <= dynasty) && (dynasty < end_dynasty x)) validators in
  filter (fun x => nth false filteredValidators x == true) indices.

(* helper function - see CrystallizedState.py *)

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

(* TODO: implement *)
Definition getRewardContext (totalDeposits : nat) (* TODO: config parameter *) : nat * nat :=
  if totalDeposits <= 0 then (* TODO: throw exception *) (0, 0) else
    (0, 0).

Definition validateAttestation (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (attestation : @AttestationRecord [ordType of Hash])
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : bool :=
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
           (blkVoteCache : BlockVoteCache) (* TODO: config paramter? *) : BlockVoteCache :=
  blkVoteCache.

Definition processBlock (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : ActiveState :=
  if all (fun x => validateAttestation crystallizedState activeState x blk cycleLength) (attestations blk) then
    (* TODO: throw exception *) activeState
  else
    (* TODO: new block vote cache *)
    let: newAtts := pending_attestations activeState ++ attestations blk in
    let: recentBlockHashes := recent_block_hashes activeState in
    (* TODO: new chain *)
    (* TODO: update activeState with newBlockVoteCache, chain *)
    @mkAS [ordType of Hash] newAtts recentBlockHashes.

(* TODO: implement *)
Definition processUpdatedCrosslinks (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block) (* TODO: config paramter? *) : seq (@CrosslinkRecord [ordType of Hash]) :=
  let: crosslinks := crosslink_records crystallizedState in
  crosslinks.

Definition calculateFfgRewards (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : seq nat :=
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

(* TODO: unimplemented in beacon_chain repo *)
Definition calculateCrosslinkRewards (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block) (* TODO: config paramter? *) : seq nat :=
  let: validators := validators crystallizedState in
  map (fun _ => 0) validators.

Definition applyRewardsAndPenalties (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : seq (@ValidatorRecord [ordType of Hash]) :=
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

Definition initializeNewCycle (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : CrystallizedState * ActiveState :=
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
  let: crosslinkRecords := processUpdatedCrosslinks crystallizedState activeState blk in
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
           (blk : block) (* TODO: config paramter? *) : ActiveState :=
  let: pendingAtts := pending_attestations activeState in
  let: newRecentBlockHashes := getNewRecentBlockHashes
                                 (recent_block_hashes activeState)
                                 (slot_number parentBlk)
                                 (slot_number blk)
                                 (parent_hash blk) in
  (* TODO: update activeState with newBlockVoteCache, chain *)
  @mkAS [ordType of Hash] pendingAtts newRecentBlockHashes.

Definition readyForDynastyTransition (crystallizedState : @CrystallizedState [ordType of Hash])
           (blk : block)
           (minDynastyLength : nat) (* TODO: config paramter? *) : bool :=
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

Definition computeDynastyTransition (crystallizedState : @CrystallizedState [ordType of Hash])
           (blk : block)
           (shardCount : nat)
           (cycleLength : nat) (* TODO: config paramter? *) : CrystallizedState :=
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

(* TODO: implement *)
(* TODO: how do we emulate the while loop? How can Coq know a parameter is decreasing? *)
Definition computeCycleTransitions (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : CrystallizedState * ActiveState :=
  (crystallizedState, activeState).

Definition computeStateTransition (crystallizedState : @CrystallizedState [ordType of Hash])
           (activeState : @ActiveState [ordType of Hash])
           (parentBlk : block)
           (blk : block)
           (cycleLength : nat) (* TODO: config paramter? *) : CrystallizedState * ActiveState :=
  let: activeState'0 := fillRecentBlockHashes activeState parentBlk blk in
  let: activeState'1 := processBlock crystallizedState activeState blk in
  computeCycleTransitions crystallizedState activeState blk cycleLength.

(* ------------------*)
(* PROTOCOL MESSAGES *)
(* ------------------*)

Definition peers_t := seq NodeId.

Inductive Message :=
| BlockMsg of block
| VoteMsg of Vote.

Inductive InternalTransition :=
  | BlockT of block
  | VoteT of Vote.

Definition eq_msg a b :=
 match a, b with
  | BlockMsg bA, BlockMsg bB => (bA == bB)
  | BlockMsg _, _ => false
  | VoteMsg vA, VoteMsg vB => (vA == vB)
  | VoteMsg _, _ => false
 end.

Ltac simple_tactic mb n n' B :=
  (case: mb=>//[b'|t'|p'|p']; do? [by constructor 2];
   case B: (n == n'); [by case/eqP:B=><-; constructor 1|constructor 2];
   case=>E; subst n'; rewrite eqxx in B).

Lemma eq_msgP : Equality.axiom eq_msg.
Proof.
move=> ma mb. rewrite/eq_msg.
case: ma=>[b|v].
- case:mb=>////[b'|v']; do? [by constructor 2].
  case B: (b == b'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst b'; rewrite eqxx in B.
- case:mb=>////[b'|v']; do? [by constructor 2].
  case B: (v == v'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst v'; rewrite eqxx in B.
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
    (* TODO: does cycleLength belong here? *)
    cycleLength : nat;
  }.

Definition initCS := @mkCS [ordType of Hash] [::] 0 [::] 0 0 0 0 [::] dummyHash 0.
Definition initAS := @mkAS [ordType of Hash] [::] [::].

Definition Init (n : NodeId) (peers : seq NodeId) : State :=
  Node n peers (#GenesisBlock \\-> GenesisBlock) initCS initAS 0.

Definition procMsg (st: @State [ordType of Hash]) (from : NodeId) (msg: Message) (ts: Timestamp) :=
  let: Node n prs bf cst ast cl := st in
  match msg with
  | BlockMsg b =>
    let: parentBlock := get_block bf (parent_hash b) in
    let: (crystallizedState, activeState) := computeStateTransition cst ast parentBlock b cl in
    let: newBf := bfExtend bf b in
    pair (Node n prs newBf crystallizedState activeState cl) emitZero
  | VoteMsg v =>
    (* process vote *)
    pair (Node n prs bf cst ast cl) emitZero
  end.

Definition procInt (st : @State [ordType of Hash]) (tr : InternalTransition) (ts : Timestamp) :=
 let: Node n prs bf cst ast cl := st in
 match tr with
 | BlockT b =>
   let: parentBlock := get_block bf (parent_hash b) in
   let: (crystallizedState, activeState) := computeStateTransition cst ast parentBlock b cl in
   let: newBf := bfExtend bf b in
   pair (Node n prs newBf crystallizedState activeState cl) (emitBroadcast n prs (BlockMsg b))
 | VoteT v =>
   (* process vote *)
   pair (Node n prs bf cst ast cl) (emitBroadcast n prs (VoteMsg v))
 end.
