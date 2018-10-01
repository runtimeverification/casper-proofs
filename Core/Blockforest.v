From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------ *)
(* BLOCKS *)
(* ------ *)

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

Record Block {Hash : ordType} {Transaction VProof : eqType} :=
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
    (* NOTE: transactions and proof not present in Danny's beacon_chain implementation *)
    txs : seq Transaction;
    proof : VProof
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
    (* The next shard that crosslinking assignment will start from *)
    crosslinking_start_shard: nat;
    (* Records about the most recent crosslink for each shard *)
    crosslink_records: seq (@CrosslinkRecord Hash);
    (* Total balance of deposits *)
    total_deposits: nat;
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

Definition eq_block {H : ordType} {T P : eqType} (b b' : @Block H T P) :=
  match b, b' with
  | mkB ph sn rr ars pcr asr csr txs p, mkB ph' sn' rr' ars' pcr' asr' csr' txs' p' =>
    [&& ph == ph', sn == sn', rr == rr', ars == ars', pcr == pcr', asr == asr',
     csr == csr', txs == txs' & p == p']
  end.
      
Lemma eq_blockP {H : ordType} {T P : eqType} : Equality.axiom (@eq_block H T P).
Proof.
case=> ph sn rr ars pcr asr csr txs p;
case=> ph' sn' rr' ars' pcr' asr' csr' txs' p'; rewrite /eq_block/=.
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
case H9: (txs == txs'); [move/eqP: H9=>?; subst txs'| constructor 2];
  last by case=>?; subst txs';rewrite eqxx in H9.
case H10: (p == p'); [move/eqP: H10=>?; subst p'| constructor 2];
  last by case=>?; subst p';rewrite eqxx in H10.
by constructor 1. 
Qed.

Canonical Block_eqMixin {H : ordType} {T P : eqType} :=
  Eval hnf in EqMixin (@eq_blockP H T P).
Canonical Block_eqType {H : ordType} {T P : eqType} :=
  Eval hnf in EqType (@Block H T P) (@Block_eqMixin H T P).

(* ------ *)
(* CHAINS *)
(* ------ *)

(* Strict version of the prefix *)
Definition is_strict_prefix {T: eqType} (bc bc' : seq T) :=
  exists b bc1, bc' = bc ++ (b :: bc1).

Notation "'[' bc1 '<<<' bc2 ']'" := (is_strict_prefix bc1 bc2).

Lemma isp_mt {T: eqType} (bc : seq T) : ~ is_strict_prefix bc [::].
Proof. by case=>b[bc1]; case: bc. Qed.

(* The corresponding checker *)
Fixpoint sprefixb {T: eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then (x == y) && (sprefixb s1' s2')
    else true
  else false.         

Lemma sprefixP {T: eqType} (bc1 bc2 : seq T):
  reflect [bc1 <<< bc2] (sprefixb bc1 bc2).
Proof.
elim: bc2 bc1=>//=[|b2 bc2 Hi/=]bc1.
- case:bc1=>//=[|b1 bc1]; constructor 2=>//; apply: isp_mt.
case: bc1=>//[|b1 bc1]/=; first by constructor 1; exists b2, bc2.  
case X: (b1 == b2)=>/=; last first.
- constructor 2=>[[p]][bc']; rewrite cat_cons; case=>Z; subst b2.
  by rewrite eqxx in X.
- move/eqP: X=>X; subst b2.
case: Hi=>H; [constructor 1|constructor 2].
- by case:H=>x[xs]->; exists x, xs; rewrite cat_cons.  
case=>x[xs]; rewrite cat_cons; case=>Z; subst bc2; apply: H.
by exists x, xs.
Qed.

(* Non-strict prefix *)
Definition is_prefix {T :eqType} (bc bc' : seq T) :=
  exists bc1, bc' = bc ++ bc1.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).

Lemma bc_pre_refl {T :eqType} (bc : seq T) : [bc <<= bc].
Proof. by exists [::]; rewrite cats0. Qed.

Lemma bc_pre_trans {T :eqType} (bc1 bc2 bc3 : seq T) :
  [bc1 <<= bc2] -> [bc2 <<= bc3] -> [bc1 <<= bc3].
Proof.
case=> a1 H1 [a2] H2; subst bc2.
by rewrite -catA in H2; exists (a1 ++ a2).
Qed.

Lemma bc_spre_nrefl {T :eqType} (bc : seq T) : ~ [bc <<< bc].
Proof.
move=>[h][t]. elim: bc=>[|x xs H]; do? by[rewrite cat0s|case].
Qed.

Lemma bc_spre_trans {T :eqType} (bc1 bc2 bc3 : seq T) :
  [bc1 <<< bc2] -> [bc2 <<< bc3] -> [bc1 <<< bc3].
Proof.
move=>[x][xs]eq [y][ys]eq'. rewrite eq' eq. clear eq eq'.
rewrite/is_strict_prefix. eexists x, (xs ++ y :: ys).
by rewrite -catA.
Qed.

Lemma bc_spre_pre {T :eqType} (bc bc' : seq T) :
  [bc <<< bc'] -> [bc <<= bc'].
Proof. by move=>[] x [] xs=>->; exists (x :: xs). Qed.

Lemma bc_pre_spre {T :eqType} (bc bc' : seq T) :
  [bc <<= bc'] -> [bc <<< bc'] \/ bc == bc'.
Proof.
case; case; first by rewrite cats0=>->; right. 
by move=>x xs->; left; eexists x, xs.
Qed.

Lemma bc_pre_both {T :eqType} (bc1 bc2 : seq T) :
  [bc1 <<= bc2] -> [bc2 <<= bc1] -> bc1 == bc2.
Proof.
move=>H1 H2. move: (bc_pre_spre H1) (bc_pre_spre H2). clear H1 H2.
case=>A; case=>B; do? by [].
by move: (bc_spre_nrefl (bc_spre_trans A B)).
by rewrite eq_sym.
Qed.

Lemma bc_spre_both {T :eqType} (bc1 bc2 : seq T) :
  sprefixb bc1 bc2 -> sprefixb bc2 bc1 -> False.
Proof.
by move/sprefixP=>A /sprefixP=>B; move: (bc_spre_nrefl (bc_spre_trans A B)).
Qed.

Lemma bc_prefix_mt {T :eqType} (bc : seq T) : [bc <<= [::]] -> bc == [::].
Proof. by case: bc=>//b bc[x]. Qed.

Lemma bc_sprefix_mt {T :eqType} (bc : seq T) : [bc <<< [::]] -> False.
Proof. by case=>x [] xs; case: bc=>//b bc[x]. Qed.
 
Fixpoint prefixb {T: eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then (x == y) && (prefixb s1' s2')
    else true
  else s1 == [::].         

Lemma bc_prefixb_mt {T :eqType} (bc : seq T) : prefixb bc [::] -> bc == [::].
Proof. by case: bc=>//b bc[x]. Qed.

Lemma prefixP {T :eqType} (bc1 bc2 : seq T):
  reflect [bc1 <<= bc2] (prefixb bc1 bc2).
Proof.
elim: bc2 bc1=>//=[|b2 bc2 Hi/=]bc1.
- case B: (prefixb bc1 [::]); [constructor 1|constructor 2].
  + by move/bc_prefixb_mt/eqP: B=>->; exists [::].
  by case: bc1 B=>//b bc1/=_[?].
case: bc1=>//[|b1 bc1]; first by constructor 1; exists (b2::bc2). 
case X: (b1 == b2)=>/=; rewrite X/=; last first.
- constructor 2=>[[p]]; rewrite cat_cons; case=>Z; subst b2.
  by rewrite eqxx in X.
- move/eqP: X=>X; subst b2.
case: Hi=>H; [constructor 1|constructor 2].
- by case:H=>x->; exists x; rewrite cat_cons.  
case=>t; rewrite cat_cons; case=>Z; subst bc2; apply: H.
by exists t.
Qed.

Lemma prb_equiv {T: eqType} (bc1 bc2 : seq T) :
  prefixb bc1 bc2 = (bc1 == bc2) || (sprefixb bc1 bc2).
Proof.
apply/Bool.eq_iff_eq_true; split.
- move/prefixP=>[x]->; case: x=>[|x xs]; first by rewrite cats0 eqxx.
  by apply/orP; right; apply/sprefixP; exists x, xs.
- move/orP; case.
  by move/eqP=><-; apply/prefixP; apply bc_pre_refl.
  by move/sprefixP=>[] x [] xs eq; apply/prefixP; rewrite eq; exists (x :: xs).
Qed.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).
Notation "'[' bc1 '<<<' bc2 ']'" := (is_strict_prefix bc1 bc2).

(* Decidable fork *)
Definition fork {T: eqType} (bc1 bc2 : seq T) :=
  ~~[|| sprefixb bc1 bc2, sprefixb bc2 bc1 | bc1 == bc2].

Definition fork_rel {T: eqType} (bc1 bc2 : seq T) :=
  ~ ([bc1 <<= bc2] \/ [bc2 <<= bc1]).

Lemma forkP {T: eqType} (bc1 bc2 : seq T) :
  reflect (fork_rel bc1 bc2) (fork bc1 bc2).
Proof.
case F: (fork bc1 bc2); [constructor 1 | constructor 2].
- move/negP: F=>F; rewrite /fork_rel=>G; apply: F.
  case: G; case=>xs; case: xs=>[| x xs]; rewrite ?cats0=>->;
  do? [by rewrite eqxx ![_ || true]orbC].
  + by apply/orP; left; apply/sprefixP; eexists _, _.  
  by apply/orP; right; apply/orP; left; apply/sprefixP; eexists _, _.
move=>G. move/negP: F=>F;apply: F. rewrite /fork_rel in G.
case/orP.
- move/sprefixP=>[x][xs]E; apply: G; subst bc2.
  by left; eexists _.
  by rewrite orbC eq_sym -prb_equiv=>P21; apply: G; right; apply/prefixP.
Qed.
  
Lemma bc_fork_neq {T: eqType} (bc bc' : seq T) :
  fork bc bc' -> bc != bc'.
Proof.
move=>H; apply/negbT/negP=>Z; move/eqP:Z=>Z; subst bc'.
by case/orP: H; right; rewrite orbC eqxx. 
Qed.

Lemma bc_fork_nrefl {T: eqType} (bc : seq T) :
  fork bc bc -> False.
Proof. by move=>H; move: (bc_fork_neq H); move/eqP. Qed.

Lemma bc_fork_sym {T: eqType} (bc bc' : seq T) :
  fork bc bc' -> fork bc' bc.
Proof.
by rewrite/fork; rewrite eq_sym orbCA.
Qed.

Lemma bc_fork_prefix {T: eqType} (a b c : seq T):
  fork a b -> [b <<= c] -> fork a c.
Proof.
move/forkP=>F H; apply/forkP; move: F H.
move/Decidable.not_or.
case=>H2 H1[x] H3; subst c.
elim: x b H1 H2=>[|x xs Hi] b H1 H2.
- by rewrite cats0; case=>H; [apply: H2|apply:H1].
rewrite -cat_rcons; apply: Hi=>H.
- by apply: H1; case: H=>z->; rewrite cat_rcons; eexists _.
- rewrite/is_prefix in H H1 H2.
case: H=>z. elim/last_ind: z=>[|zs z Hi].
- by rewrite cats0=>Z; subst a; apply: H1; exists [:: x]; rewrite cats1.
rewrite -rcons_cat=>/eqP; rewrite eqseq_rcons; move/andP=>[/eqP Z]/eqP Z'.
by subst x b; apply: H2; exists zs.
Qed.

Inductive bc_rel {T : eqType} (bc bc' : seq T) : bool-> bool-> bool-> bool-> Set :=
| CmpBcEq of bc == bc' : bc_rel bc bc' true false false false
| CmpBcFork of fork bc bc' : bc_rel bc bc' false true false false
| CmpBcPre12 of sprefixb bc bc' : bc_rel bc bc' false false true false
| CmpBcPre21 of sprefixb bc' bc: bc_rel bc bc' false false false true.

Lemma bc_relP {T : eqType} (bc bc' : seq T) :
  bc_rel bc bc' (bc == bc') (fork bc bc') (sprefixb bc bc') (sprefixb bc' bc).
Proof.
case Eq: (bc == bc'); case F: (fork bc bc');
case S12: (sprefixb bc bc'); case S21: (sprefixb bc' bc);
do? by [
  constructor |
  contradict Eq; move: (bc_fork_neq F)=>/eqP=>A B; apply A; move/eqP in B |
  contradict Eq; move: (bc_spre_both S12 S21) |
  contradict S12; move/eqP: Eq=><-=>/sprefixP; apply: bc_spre_nrefl |
  contradict S21; move/eqP: Eq=><-=>/sprefixP; apply: bc_spre_nrefl
].
- by contradict F; move/norP=>[] C; rewrite S12 in C.
- by contradict F; move/norP=>[] _=>/norP; elim=>C; rewrite S21 in C.
- by contradict F; rewrite/fork Eq S12 S21.
Qed.

(* -----------*)
(* BLOCK DATA *)
(* -----------*)

Parameter Timestamp : Type.
Parameter Hash : finType.
Parameter VProof : eqType.

Parameter NodeId : finType.

Definition ValidatorIndex := nat.
Definition Wei := nat.
Definition Epoch := nat.
Definition Dynasty := nat.

(* casper payload signature *)
Parameter Signature : eqType.

(* Deposit(VALIDATION_ADDR, WITHDRAWAL_ADDR, DEPOSIT) *)

Record Deposit :=
  mkDeposit {
   deposit_validation_addr : Sender;
   deposit_withdrawal_addr : Sender;
   deposit_amount : Wei
  }.

(* Vote(VALIDATOR_INDEX, TARGET_HASH, TARGET_EPOCH, SOURCE_EPOCH, SIG) *)

Record Vote :=
  mkVote {
    vote_validator_index : ValidatorIndex;
    vote_target_hash : Hash;
    vote_target_epoch : Epoch;
    vote_source_epoch : Epoch;
    vote_sig : Signature
  }.

(* Logout(VALIDATOR_INDEX, EPOCH, SIG) *)

Record Logout :=
  mkLogout {
    logout_validator_index : ValidatorIndex;
    logout_epoch : Epoch;
    logout_sig : Signature
  }.

Inductive ContractCall :=
| DepositCall of Deposit
| VoteCall of Vote
| LogoutCall of Logout
| WithdrawCall of ValidatorIndex
| InitializeEpochCall of Epoch
| SlashCall of Vote & Vote.

Record Transaction :=
 mkTx {
   tx_sender : Sender;
   tx_call : ContractCall
 }.

Record SendAccount :=
 mkSA {
   send_account_addr : Sender;
   send_account_wei : Wei
 }.

Definition eq_Deposit (d d' : Deposit) :=
  match d, d' with
  | mkDeposit va1 wa1 am1, mkDeposit va2 wa2 am2 =>
    [&& va1 == va2, wa1 == wa2 & am1 == am2]
  end.

Lemma eq_DepositP : Equality.axiom eq_Deposit.
Proof.
case => va1 wa1 am1; case => va2 wa2 am2; rewrite /eq_Deposit/=.
case H2: (va1 == va2); [move/eqP: H2=>?; subst va2| constructor 2];
  last by case=>?; subst va2;rewrite eqxx in H2.
case H3: (wa1 == wa2); [move/eqP: H3=>?; subst wa2| constructor 2];
  last by case=>?; subst wa2;rewrite eqxx in H3.
case H4: (am1 == am2); [move/eqP: H4=>?; subst am2| constructor 2];
  last by case=>?; subst am2;rewrite eqxx in H4.
by constructor 1.
Qed.

Definition Deposit_eqMixin :=
  Eval hnf in EqMixin eq_DepositP.
Canonical Deposit_eqType :=
  Eval hnf in EqType Deposit Deposit_eqMixin.

Definition eq_Vote (v v' : Vote) :=
  match v, v' with
  | mkVote v1 th1 te1 se1 sg1, mkVote v2 th2 te2 se2 sg2 =>
    [&& v1 == v2, th1 == th2, te1 == te2, se1 == se2 & sg1 == sg2]
  end.

Lemma eq_VoteP : Equality.axiom eq_Vote.
Proof.
case => v1 th1 te1 se1 sg1; case => v2 th2 te2 se2 sg2; rewrite /eq_Vote/=.
case H2: (v1 == v2); [move/eqP: H2=>?; subst v2| constructor 2];
  last by case=>?; subst v2;rewrite eqxx in H2.
case H3: (th1 == th2); [move/eqP: H3=>?; subst th2| constructor 2];
  last by case=>?; subst th2;rewrite eqxx in H3.
case H4: (te1 == te2); [move/eqP: H4=>?; subst te2| constructor 2];
  last by case=>?; subst te2;rewrite eqxx in H4.
case H5: (se1 == se2); [move/eqP: H5=>?; subst se2| constructor 2];
  last by case=>?; subst se2;rewrite eqxx in H5.
case H6: (sg1 == sg2); [move/eqP: H6=>?; subst sg2| constructor 2];
  last by case=>?; subst sg2;rewrite eqxx in H6.
by constructor 1.
Qed.

Definition Vote_eqMixin :=
  Eval hnf in EqMixin eq_VoteP.
Canonical Vote_eqType :=
  Eval hnf in EqType Vote Vote_eqMixin.

Definition eq_Logout (l l' : Logout) :=
match l, l' with
| mkLogout v1 e1 s1, mkLogout v2 e2 s2 =>
  [&& v1 == v2, e1 == e2 & s1 == s2]
end.

Lemma eq_LogoutP : Equality.axiom eq_Logout.
Proof.
case => la1 le1 ls1; case => la2 le2 ls2; rewrite /eq_Logout/=.
case H2: (la1 == la2); [move/eqP: H2=>?; subst la2| constructor 2];
  last by case=>?; subst la2;rewrite eqxx in H2.
case H3: (le1 == le2); [move/eqP: H3=>?; subst le2| constructor 2];
  last by case=>?; subst le2;rewrite eqxx in H3.
case H4: (ls1 == ls2); [move/eqP: H4=>?; subst ls2| constructor 2];
  last by case=>?; subst ls2;rewrite eqxx in H4.
by constructor 1.
Qed.

Definition Logout_eqMixin :=
  Eval hnf in EqMixin eq_LogoutP.
Canonical Logout_eqType :=
  Eval hnf in EqType Logout Logout_eqMixin.

Definition eq_ContractCall c1 c2 :=
  match c1, c2 with
  | DepositCall d1, DepositCall d2 => (d1 == d2)
  | DepositCall _, _ => false
  | VoteCall v1, VoteCall v2 => (v1 == v2)
  | VoteCall _, _ => false
  | LogoutCall l1, LogoutCall l2 => (l1 == l2)
  | LogoutCall _, _ =>  false
  | WithdrawCall v1, WithdrawCall v2 => (v1 == v2)
  | WithdrawCall _, _ => false
  | InitializeEpochCall e1, InitializeEpochCall e2 => (e1 == e2)
  | InitializeEpochCall _, _ => false
  | SlashCall v1 v2, SlashCall v'1 v'2 => [&& v1 == v'1 & v2 == v'2]
  | SlashCall _ _, _ => false
  end.

Lemma eq_ContractCallP : Equality.axiom eq_ContractCall.
Proof.
move=> c1 c2. rewrite/eq_ContractCall.
case: c1=>[d1|v1|l1|vi1|e1|v11 v12].
- case:c2=>////[d2|v2|l2|vi2|e2|v'1 v'2]; do? [by constructor 2].
  case B: (d1 == d2); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst d2; rewrite eqxx in B.
- case:c2=>////[d2|v2|l2|vi2|e2|v'1 v'2]; do? [by constructor 2].
  case B: (v1 == v2); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst v2; rewrite eqxx in B.
- case:c2=>////[d2|v2|l2|vi2|e2|v'1 v'2]; do? [by constructor 2].
  case B: (l1 == l2); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst l2; rewrite eqxx in B.
- case:c2=>////[d2|v2|l2|vi2|e2|v'1 v'2]; do? [by constructor 2].
  case B: (vi1 == vi2); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst vi2; rewrite eqxx in B.
- case:c2=>////[d2|v2|l2|vi2|e2|v'1 v'2]; do? [by constructor 2].
  case B: (e1 == e2); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst e2; rewrite eqxx in B.
- case:c2=>////[d2|v2|l2|vi2|e2|v21 v22]; do? [by constructor 2].
  case B1: (v11 == v21); case B2: (v12 == v22); [|constructor 2|constructor 2|constructor 2].
  * by case/eqP: B1=><-; case/eqP: B2=><-; constructor 1.
  * by case => H_eq H_eq'; subst v22; rewrite eqxx in B2.
  * by case => H_eq H_eq'; subst v21; rewrite eqxx in B1.
  * by case => H_eq H_eq'; subst v22; rewrite eqxx in B2.
Qed.

Definition ContractCall_eqMixin :=
  Eval hnf in EqMixin eq_ContractCallP.
Canonical ContractCall_eqType :=
  Eval hnf in EqType ContractCall ContractCall_eqMixin.

Definition eq_Transaction t1 t2 :=
  [&& tx_sender t1 == tx_sender t2 & tx_call t1 == tx_call t2].

Lemma eq_TransactionP : Equality.axiom eq_Transaction.
Proof.
case => s1 c1; case => s2 c2; rewrite /eq_Transaction /=.
case B1: (s1 == s2); case B2: (c1 == c2); [|constructor 2|constructor 2|constructor 2].
- by case/eqP: B1=><-; case/eqP: B2=><-; constructor 1.
- by case => H_eq H_eq'; subst c2; rewrite eqxx in B2.
- by case => H_eq H_eq'; subst s2; rewrite eqxx in B1.
- by case => H_eq H_eq'; subst c2; rewrite eqxx in B2.
Qed.

Definition Transaction_eqMixin :=
  Eval hnf in EqMixin eq_TransactionP.
Canonical Transaction_eqType :=
  Eval hnf in EqType Transaction Transaction_eqMixin.

Definition eq_SendAccount s1 s2 :=
  [&& send_account_addr s1 == send_account_addr s2 & send_account_wei s1 == send_account_wei s2].

Lemma eq_SendAccountP : Equality.axiom eq_SendAccount.
Proof.
case => a1 w1; case => a2 w2; rewrite /eq_SendAccount /=.
case B1: (a1 == a2); case B2: (w1 == w2); [|constructor 2|constructor 2|constructor 2].
- by case/eqP: B1=><-; case/eqP: B2=><-; constructor 1.
- by case => H_eq H_eq'; subst w2; rewrite eqxx in B2.
- by case => H_eq H_eq'; subst a2; rewrite eqxx in B1.
- by case => H_eq H_eq'; subst w2; rewrite eqxx in B2.
Qed.

Definition SendAccount_eqMixin :=
  Eval hnf in EqMixin eq_SendAccountP.
Canonical SendAccount_eqType :=
  Eval hnf in EqType SendAccount SendAccount_eqMixin.

Definition Hash_ordMixin := fin_ordMixin Hash.
Canonical Hash_finType := Eval hnf in OrdType Hash Hash_ordMixin.

(* --------------*)
(* BLOCK FORESTS *)
(* --------------*)

Definition block := @Block [ordType of Hash] [eqType of Transaction] VProof.

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

Definition Blockforest := union_map [ordType of Hash] block.

Definition TxPool := seq Transaction.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : NodeId -> Blockchain -> TxPool -> Timestamp -> option VProof.
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.
Parameter blockNumber : block -> nat.

Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> Blockforest -> Transaction -> TxPool.

Parameter sigValid_epoch : Sender -> ValidatorIndex -> Epoch -> Signature -> bool.
Parameter sigValid_epochs : Sender -> ValidatorIndex -> Hash -> Epoch -> Epoch -> Signature -> bool.

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).
Notation "# b" := (hashB b) (at level 20).

Axiom hashB_inj : injective hashB.

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition bfHasBlock (bf : Blockforest) (b : block) := #b \in dom bf.

Notation "b ∈ bf" := (bfHasBlock bf b) (at level 70).
Notation "b ∉ bf" := (~~ bfHasBlock bf b) (at level 70).

Definition valid_block b : bool :=
  parent_hash b != #b.

Definition has_init_block (bf : Blockforest) :=
  find (# GenesisBlock) bf = Some GenesisBlock.

Definition validH (bf : Blockforest) :=
  forall h b, find h bf = Some b -> h = hashB b.

Lemma validH_free bf (b : block) :
  validH bf -> validH (free (# b) bf).
Proof. by move=>Vh h c; rewrite findF;case: ifP=>//_ /Vh. Qed.

(* We only add "fresh blocks" *)
Definition bfExtend (bf : Blockforest) (b : block) :=
  if #b \in dom bf then bf else #b \\-> b \+ bf.

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

Definition valid_chain_block bc (b : block) :=
  [&& VAF (proof b) bc (txs b) & all [pred t | txValid t bc] (txs b)].

(* All paths/chains should start with the GenesisBlock *)
Fixpoint compute_chain' (bf : Blockforest) b remaining n : Blockchain :=
  (* Preventing cycles in chains *)
  if (hashB b) \in remaining
  then
    let rest := seq.rem (hashB b) remaining in
    (* Supporting primitive inductions *)
    if n is n'.+1 then
      match find (parent_hash b) bf with
      (* No parent *)
      | None => [:: b]
      (* Build chain prefix recursively *)
      | Some prev =>
        rcons (nosimpl (compute_chain' (free (hashB b) bf) prev rest n')) b
      end
    else [::]
  else [::].

(* Compute chain from the block *)
Definition compute_chain bf b :=
  compute_chain' bf b (dom bf) (size (dom bf)).

(* Total get_block function *)
Definition get_block (bf : Blockforest) k : Block :=
  if find k bf is Some b then b else GenesisBlock.

(* Collect all blocks *)
Definition all_blocks (bf : Blockforest) := [seq get_block bf k | k <- dom bf].

Definition is_block_in (bf : Blockforest) b := exists k, find k bf = Some b.

(* A certificate for all_blocks *)
Lemma all_blocksP bf b : reflect (is_block_in bf b) (b \in all_blocks bf).
Proof.
case B : (b \in all_blocks bf); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  move/um_eta: Ik=>[b]/=[E H].
  by exists k; rewrite /get_block E.
case=>k F; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists k; last by rewrite /get_block F.
by move/find_some: F.
Qed.

Lemma all_blocksP' bf b : validH bf -> reflect (b ∈ bf) (b \in all_blocks bf).
Proof.
move=>Vh.
case B : (b \in all_blocks bf); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  move/um_eta: Ik=>[b]/=[E H].
  rewrite/get_block E /bfHasBlock; specialize (Vh _ _ E); subst k.
  by move: (find_some E).
case=>H; rewrite/bfHasBlock; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists (#b); first by [].
rewrite/bfHasBlock in H; rewrite/get_block.
case X: (find _ _)=>[b'|].
by move: (Vh _  _ X); move/hashB_inj.
by contradict H; move: (find_none X)=>H; apply/negP.
Qed.

(* All chains from the given forest *)
Definition good_chain (bc : Blockchain) :=
  if bc is h :: _ then h == GenesisBlock else false.

(* Transaction validity *)
Fixpoint valid_chain' (bc prefix : seq block) :=
  if bc is b :: bc'
  then [&& VAF (proof b) prefix (txs b) && all [pred t | txValid t prefix] (txs b) & valid_chain' bc' (rcons prefix b)]
  else true.

Definition valid_chain bc := valid_chain' bc [::].

Definition all_chains bf := [seq compute_chain bf b | b <- all_blocks bf].

Definition good_chains bf := [seq c <- all_chains bf | good_chain c && valid_chain c].

(* Get the blockchain *)
Definition take_better_bc bc2 bc1 :=
  if (good_chain bc2 && valid_chain bc2) && (bc2 > bc1) then bc2 else bc1.

Definition bfChain bf : Blockchain :=
  foldr take_better_bc [:: GenesisBlock] (all_chains bf).

(* HELPERS *)

Definition set_crystallized_state_validators a v := @mkCS [ordType of Hash] v (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_last_state_recalc a v := @mkCS [ordType of Hash] (validators a) v (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_shard_and_committee_for_slots a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) v (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_last_justified_slot a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) v (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_justified_streak a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) v (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_last_finalized_slot a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) v (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_current_dynasty a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) v (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_crosslinking_start_shard a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) v (crosslink_records a) (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_crosslink_records a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) v (total_deposits a) (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_total_deposits a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) v (dynasty_seed a) (dynasty_start a).
Definition set_crystallized_state_dynasty_seed a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) v (dynasty_start a).
Definition set_crystallized_state_dynasty_start a v := @mkCS [ordType of Hash] (validators a) (last_state_recalc a) (shard_and_committee_for_slots a) (last_justified_slot a) (justified_streak a) (last_finalized_slot a) (current_dynasty a) (crosslinking_start_shard a) (crosslink_records a) (total_deposits a) (dynasty_seed a) v.

Notation "{[ a 'with' 'validators' := v ]}" := (set_crystallized_state_validators a v).
Notation "{[ a 'with' 'last_state_recalc' := v ]}" := (set_crystallized_state_last_state_recalc a v).
Notation "{[ a 'with' 'shard_and_committee_for_slots' := v ]}" := (set_crystallized_state_shard_and_committee_for_slots a v).
Notation "{[ a 'with' 'last_justified_slot' := v ]}" := (set_crystallized_state_last_justified_slot a v).
Notation "{[ a 'with' 'justified_streak' := v ]}" := (set_crystallized_state_justified_streak a v).
Notation "{[ a 'with' 'last_finalized_slot' := v ]}" := (set_crystallized_state_last_finalized_slot a v).
Notation "{[ a 'with' 'current_dynasty' := v ]}" := (set_crystallized_state_current_dynasty a v).
Notation "{[ a 'with' 'crosslinking_start_shard' := v ]}" := (set_crystallized_state_crosslinking_start_shard a v).
Notation "{[ a 'with' 'crosslink_records' := v ]}" := (set_crystallized_state_crosslink_records a v).
Notation "{[ a 'with' 'total_deposits' := v ]}" := (set_crystallized_state_total_deposits a v).
Notation "{[ a 'with' 'dynasty_seed' := v ]}" := (set_crystallized_state_dynasty_seed a v).
Notation "{[ a 'with' 'dynasty_start' := v ]}" := (set_crystallized_state_dynasty_start a v).

Arguments set_crystallized_state_validators  _ _/.
Arguments set_crystallized_state_last_state_recalc  _ _/.
Arguments set_crystallized_state_shard_and_committee_for_slots  _ _/.
Arguments set_crystallized_state_last_justified_slot  _ _/.
Arguments set_crystallized_state_justified_streak  _ _/.
Arguments set_crystallized_state_last_finalized_slot  _ _/.
Arguments set_crystallized_state_current_dynasty  _ _/.
Arguments set_crystallized_state_crosslinking_start_shard  _ _/.
Arguments set_crystallized_state_crosslink_records  _ _/.
Arguments set_crystallized_state_total_deposits  _ _/.
Arguments set_crystallized_state_dynasty_seed  _ _/.
Arguments set_crystallized_state_dynasty_start  _ _/.

Definition set_validator_record_pubkey a v := @mkVR [ordType of Hash] v (withdrawal_shard a) (withdrawal_address a) (randao_commitment a) (balance a) (start_dynasty a) (end_dynasty a).
Definition set_validator_record_withdrawal_shard a v := @mkVR [ordType of Hash] (pubkey a) v (withdrawal_address a) (randao_commitment a) (balance a) (start_dynasty a) (end_dynasty a).
Definition set_validator_record_withdrawal_address a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) v (randao_commitment a) (balance a) (start_dynasty a) (end_dynasty a).
(* TODO: implicit parameter Hash *)
(*Definition set_validator_record_randao_commitment a v := @mkVR [ordType of Hash] (pubkey a) (withdrawal_shard a) (withdrawal_address a) v (balance a) (start_dynasty a) (end_dynasty a).*)
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
