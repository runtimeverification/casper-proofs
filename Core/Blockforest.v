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

Parameter Hash : finType.
Parameter NodeId : finType.
Parameter Timestamp : Type.

Definition Hash_ordMixin := fin_ordMixin Hash.
Canonical Hash_finType := Eval hnf in OrdType Hash Hash_ordMixin.

(* --------------*)
(* BLOCK FORESTS *)
(* --------------*)

Definition block := @Block [ordType of Hash].

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

Definition Blockforest := union_map [ordType of Hash] block.

Parameter hashB : block -> Hash.
Parameter FCR : Blockchain -> Blockchain -> bool.

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

(* Definition valid_chain_block bc (b : block) :=
  [&& VAF (proof b) bc (txs b) & all [pred t | txValid t bc] (txs b)]. *)

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

Definition all_chains bf := [seq compute_chain bf b | b <- all_blocks bf].

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
