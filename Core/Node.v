From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype div path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import Blockforest Casper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition NodeId_ordMixin := fin_ordMixin NodeId.
Canonical NodeId_ordType := Eval hnf in OrdType NodeId NodeId_ordMixin.

(* -----------------*)
(* CASPER FUNCTIONS *)
(* -----------------*)

(* FIXME: implement *)
Definition setZero (deposits : union_map [ordType of Epoch] Wei) :=
  deposits.

Definition deleteValidator (validator_index : ValidatorIndex) (validators : union_map [ordType of ValidatorIndex] ValidatorData) :=
  if find validator_index validators is Some validator then
    let: deposits := validator.(validator_deposit) in
    let: validator'0 := {[ validator with validator_start_dynasty := 0 ]} in
    let: validator'1 := {[ validator'0 with validator_end_dynasty := 0 ]} in
    (* FIXME: 0 values for addresses? *)
    (* let: validator'2 := {[ validator'1 with validator_addr := 0 ]} in *)
    (* let: validator'3 := {[ validator'2 with validator_withdrawal_addr := 0 ]} in *)
    let: validator'2 := {[ validator'1 with validator_deposit := setZero(deposits) ]} in
    validator_index \\-> validator'2 \+ validators
  else
    validators.

(* FIXME: implement *)
Definition updateDeposit (validators : union_map [ordType of ValidatorIndex] ValidatorData) (current_epoch : Epoch) (addition : Wei) :=
validators.

(* FIXME: implement *)
Definition reward (validator_index : ValidatorIndex) (source_epoch : Epoch) (st : CasperData) :=
  st.

(* FIXME: implement *)
Definition justify (target_epoch : Epoch) (source_epoch : Epoch) (st : CasperData) :=
  st.

Definition finalize (target_epoch : Epoch) (source_epoch : Epoch) (st : CasperData) :=
  let: epochs := st.(casper_epochs) in
  if find source_epoch epochs is Some source_epoch_data then
    if target_epoch == source_epoch + 1 then
      let: epoch_data' := {[ source_epoch_data with epoch_is_finalized := true ]} in
      let: epochs' := upd target_epoch epoch_data' epochs in
      let: st'0 := {[ st with casper_epochs := epochs' ]} in
      let: st'1 := {[ st'0 with casper_last_finalized_epoch := source_epoch ]} in
      st'1
    else
      st
  else
    st.

(* FIXME: implement *)
Definition send (withdrawal_addr : Address) (amount : Wei) (st : CasperData) :=
  st.

Definition incrementDynasty (st : CasperData) :=
  let: epochs := st.(casper_epochs) in
  let: current_epoch := st.(casper_current_epoch) in
  let: dec_epoch := current_epoch.-2 in
  let: current_dynasty := st.(casper_current_dynasty) in
  let: dynasty_start_epoch := st.(casper_dynasty_start_epoch) in
  if 2 <= current_epoch then
    if find dec_epoch epochs is Some dec_epoch_data then
      if dec_epoch_data.(epoch_is_finalized) then
        let: new_current_dynasty := current_dynasty.+1 in
        let: st'0 := {[ st with casper_current_dynasty := new_current_dynasty ]} in
        let: dynasty_start_epoch' := upd new_current_dynasty current_epoch dynasty_start_epoch in
        let: st'1 := {[ st'0 with casper_dynasty_start_epoch := dynasty_start_epoch' ]} in
        st'1
      else
        (* No change if not finalized *)
        st
    else
      (* FIXME: error here? *)
      st
  else
    (* FIXME: report error here, and other places where we do not match? *)
    st.

Definition procContractCallTx (block_number : nat) (t : Transaction) (st : CasperData) : CasperData * seq SendAccount :=
  let: sender := t.(tx_sender) in
  let: validators := st.(casper_validators) in
  let: epochs := st.(casper_epochs) in
  let: current_epoch := st.(casper_current_epoch) in
  let: current_dynasty := st.(casper_current_dynasty) in
  let: next_validator_index := st.(casper_next_validator_index) in
  let: dynasty_start_epoch := st.(casper_dynasty_start_epoch) in
  match t.(tx_call) with
  | DepositCall d =>
    (* check non-null sender *)
    if sender is AddrSender sender_addr then
      let: amount := d.(deposit_amount) in
      let: valid_block_epoch := current_epoch == block_number %/ casper_epoch_length in
      let: valid_amount := casper_min_deposit_size <= amount in
      if [&& valid_block_epoch & valid_amount] then
        let: deposits := st.(casper_current_dynasty) \\-> amount in
        let: validation_addr := d.(deposit_validation_addr) in
        let: withdrawal_addr := d.(deposit_withdrawal_addr) in
        let: start_dynasty := st.(casper_current_epoch).+2 in
        let: validator_data := mkValidatorData validation_addr withdrawal_addr deposits start_dynasty casper_default_end_dynasty in
        let: validators' := next_validator_index \\-> validator_data \+ validators in
        let: st'0 := {[ st with casper_validators := validators' ]} in
        let: st'1 := {[ st'0 with casper_next_validator_index := next_validator_index.+1 ]} in
        (st'1, [::])
      else
        (st, [::])
    else
      (st, [::])

  | VoteCall v =>
    let: validator_index := v.(vote_validator_index) in
    let: target_hash := v.(vote_target_hash) in
    let: target_epoch := v.(vote_target_epoch) in
    let: source_epoch := v.(vote_source_epoch) in
    let: sig := v.(vote_sig) in
    (* look up validator *)
    if find validator_index validators is Some validator then
      let: validation_addr := validator.(validator_addr) in
      (* look up epoch *)
      if find target_epoch epochs is Some target_epoch_data then
        let: voted := target_epoch_data.(epoch_voted) in
        if find source_epoch epochs is Some source_epoch_data then
          (* check that source epoch is justified *)
          if source_epoch_data.(epoch_is_justified) then
            (* check that validator_index has not already voted *)
            if validator_index \notin voted then
              (* check that signature is valid *)
              let: valid_sig := sigValid_epochs validation_addr validator_index target_hash target_epoch source_epoch sig in
              if valid_sig then
                let: voted' := rcons voted validator_index in
                let: epoch_data' := {[ target_epoch_data with epoch_voted := voted' ]} in
                let: epochs' := upd target_epoch epoch_data' epochs in
                let: st'0 := {[ st with casper_epochs := epochs' ]} in
                let: st'1 := reward validator_index source_epoch st'0 in
                let: st'2 := justify target_epoch source_epoch st'1 in
                let: st'3 := finalize target_epoch source_epoch st'2 in
                (st'3, [::])
              else
                (st, [::])
            else
              (st, [::])
          else
            (st, [::])
        else
          (st, [::])
      else
        (st, [::])
    else
      (st, [::])

  | LogoutCall l =>
    (* check non-null sender *)
    if sender is AddrSender sender_addr then
      let: validator_index := l.(logout_validator_index) in
      let: epoch := l.(logout_epoch) in
      let: sig := l.(logout_sig) in
      (* look up validator *)
      if find validator_index validators is Some validator then
        let: addr := validator.(validator_addr) in
        let: end_dynasty := current_dynasty + casper_dynasty_logout_delay in
        let: validator_end_dynasty := validator.(validator_end_dynasty) in
        let: valid_block_epoch := current_epoch == block_number %/ casper_epoch_length in
        let: valid_epoch := epoch <= current_epoch in
        let: valid_sig := sigValid_epoch addr validator_index epoch sig in
        let: valid_dynasty := end_dynasty < validator_end_dynasty in
        if [&& valid_block_epoch, valid_epoch, valid_sig & valid_dynasty] then
          let validator' := {[ validator with validator_end_dynasty := end_dynasty ]} in
          let validators' := validator_index \\-> validator' \+ validators in
          let: st' := {[ st with casper_validators := validators' ]} in
          (* TODO: update dynasty_wei_delta *)
          (st', [::])
        else
          (st, [::])
      else
        (st, [::])
    else
      (st, [::])

  | WithdrawCall validator_index =>
    (* check non-null sender *)
    if sender is AddrSender sender_addr then
      (* look up validator *)
      if find validator_index validators is Some validator then
        let: validator_deposit := validator.(validator_deposit) in
        let: validator_withdrawal_addr := validator.(validator_withdrawal_addr) in
        let: validator_end_dynasty := validator.(validator_end_dynasty) in
        (* look up end epoch of validator *)
        if find validator_end_dynasty.+1 dynasty_start_epoch is Some end_epoch then
          (* look up validator deposit for end epoch *)
          if find end_epoch validator_deposit is Some deposit then
            let: valid_dynasty := validator_end_dynasty.+1 <= current_dynasty in
            let: valid_epoch := end_epoch + casper_withdrawal_delay <= current_epoch in
            if [&& valid_dynasty & valid_epoch] then
              (* delete validator information *)
              let: validators' := deleteValidator validator_index validators in
              (* return deposit *)
              let: st'0 := {[ st with casper_validators := validators' ]} in
              let: st'1 := send validator_withdrawal_addr deposit st'0 in
              let: sa' := [:: mkSA validator_withdrawal_addr deposit] in
              (st'1, sa')
            else
              (st, [::])
          else
            (st, [::])
        else
          (st, [::])
      else
        (st, [::])
    else
      (st, [::])

  | InitializeEpochCall e =>
    (st, [::])

  | SlashCall v1 v2 =>
    (* check non-null sender *)
    if sender is AddrSender sender_addr then
      let: validator_index_1 := v1.(vote_validator_index) in
      let: validator_index_2 := v2.(vote_validator_index) in
      let: target_hash_1 := v1.(vote_target_hash) in
      let: target_hash_2 := v2.(vote_target_hash) in
      let: target_epoch_1 := v1.(vote_target_epoch) in
      let: target_epoch_2 := v2.(vote_target_epoch) in
      let: source_epoch_1 := v1.(vote_source_epoch) in
      let: source_epoch_2 := v2.(vote_source_epoch) in
      let: sig_1 := v1.(vote_sig) in
      let: sig_2 := v2.(vote_sig) in
      (* look up validator *)
      if find validator_index_1 validators is Some validator then
        let: validator_deposit := validator.(validator_deposit) in
        let: validator_addr := validator.(validator_addr) in
        (* look up deposit for validator in current epoch *)
        if find current_epoch validator_deposit is Some deposit then
          let: valid_sig_1 := sigValid_epochs validator_addr validator_index_1 target_hash_1 target_epoch_1 source_epoch_1 sig_1 in
          let: valid_sig_2 := sigValid_epochs validator_addr validator_index_2 target_hash_2 target_epoch_2 source_epoch_2 sig_2 in
          let: valid_indexes := validator_index_1 == validator_index_2 in
          let: valid_hashes_epochs := ~~[&& target_hash_1 == target_hash_2, target_epoch_1 == target_epoch_2 & source_epoch_1 == source_epoch_2] in
          let: epoch_cond_1 := [&& target_epoch_2 < target_epoch_1 & source_epoch_1 < source_epoch_2] in
          let: epoch_cond_2 := [&& target_epoch_1 < target_epoch_2 & source_epoch_2 < source_epoch_1] in
          let: valid_targets := [|| target_epoch_1 == target_epoch_2, epoch_cond_1 | epoch_cond_2] in
          if [&& valid_sig_1, valid_sig_2, valid_indexes, valid_hashes_epochs & valid_targets] then
            let: validators' := deleteValidator validator_index_1 validators in
            let: st'0 := {[ st with casper_validators := validators' ]} in
            let: st'1 := send sender_addr (deposit %/ 25) st'0 in
            let: sa' := [:: mkSA sender_addr deposit] in (* FIXME: scale factor? *)
            (st'1, sa')
          else
            (st, [::])
        else
          (st, [::])
      else
        (st, [::])
    else
      (st, [::])

  end.

Definition procContractCallBlock_aux (block_number : nat) (t: Transaction) (ps : CasperData * seq SendAccount) : CasperData * seq SendAccount :=
  let: ps' := procContractCallTx block_number t ps.1 in
  (ps'.1, ps.2 ++ ps'.2).

Definition procContractCallBlock (b : block) (ps : CasperData * seq SendAccount) : CasperData * seq SendAccount :=
  foldr (procContractCallBlock_aux (blockNumber b)) ps b.(txs).

Definition casper_state_bc (init : CasperData) (bc : Blockchain) : CasperData * seq SendAccount :=
  foldr procContractCallBlock (init, [::]) bc.

Definition casper_state_bc_init (bc : Blockchain) : CasperData * seq SendAccount :=
  casper_state_bc InitCasperData bc.

(* ------------------*)
(* PROTOCOL MESSAGES *)
(* ------------------*)

Definition peers_t := seq NodeId.

Inductive Message :=
| BlockMsg of block
| TxMsg of Transaction
| InvMsg of seq Hash
| GetDataMsg of Hash.

Inductive InternalTransition :=
  | TxT of Transaction
  | MintT.

Definition eq_msg a b :=
 match a, b with
  | BlockMsg bA, BlockMsg bB => (bA == bB)
  | BlockMsg _, _ => false
  | TxMsg tA, TxMsg tB => (tA == tB)
  | TxMsg _, _ => false
  | InvMsg hA, InvMsg hB => (hA == hB)
  | InvMsg _, _ => false
  | GetDataMsg hA, GetDataMsg hB => (hA == hB)
  | GetDataMsg _, _ => false
 end.

Ltac simple_tactic mb n n' B :=
  (case: mb=>//[b'|t'|p'|p']; do? [by constructor 2];
   case B: (n == n'); [by case/eqP:B=><-; constructor 1|constructor 2];
   case=>E; subst n'; rewrite eqxx in B).

Lemma eq_msgP : Equality.axiom eq_msg.
Proof.
move=> ma mb. rewrite/eq_msg.
case: ma=>[b|t|h|h].
- case:mb=>////[b'|t'|h'|h']; do? [by constructor 2].
  case B: (b == b'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst b'; rewrite eqxx in B.
- case:mb=>////[b'|t'|h'|h']; do? [by constructor 2].
  case B: (t == t'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst t'; rewrite eqxx in B.
- case:mb=>////[b'|t'|h'|h']; do? [by constructor 2].
  case B: (h == h'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst h'; rewrite eqxx in B.
- case:mb=>////[b'|t'|h'|h']; do? [by constructor 2].
  case B: (h == h'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst h'; rewrite eqxx in B.
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

Record State :=
  Node {
    id : NodeId;
    peers : peers_t;
    blocks : Blockforest;
    txPool : TxPool;
  }.

Definition Init (n : NodeId) (peers : seq NodeId) : State :=
  Node n peers (#GenesisBlock \\-> GenesisBlock) [::].

Definition procMsg (st: State) (from : NodeId) (msg: Message) (ts: Timestamp) :=
    let: Node n prs bf pool := st in
    match msg with
    | BlockMsg b =>
      let: newBf := bfExtend bf b in
      let: newPool := [seq t <- pool | txValid t (bfChain newBf)] in
      let: ownHashes := dom newBf ++ [seq hashT t | t <- newPool] in
      pair (Node n prs newBf newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | TxMsg tx =>
      let: newPool := tpExtend pool bf tx in
      let: ownHashes := dom bf ++ [seq hashT t | t <- newPool] in
      pair (Node n prs bf newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | InvMsg peerHashes =>
      let: ownHashes := dom bf ++ [seq hashT t | t <- pool] in
      let: newH := [seq h <- peerHashes | h \notin ownHashes] in
      let: gets := [seq mkP n from (GetDataMsg h) | h <- newH] in
      pair st (emitMany gets)

    | GetDataMsg h =>
      (* Do not respond to yourself *)
      if from == n then pair st emitZero else
      let: matchingBlocks := [seq b <- [:: get_block bf h] | b != GenesisBlock] in
      match ohead matchingBlocks with
      | Some b => pair (Node n prs bf pool) (emitOne (mkP n from (BlockMsg b)))
      | None =>
        let: matchingTxs := [seq t <- pool | (hashT t) == h] in
        match ohead matchingTxs with
        | Some tx =>
          pair (Node n prs bf pool) (emitOne (mkP n from (TxMsg tx)))
        | None => pair st emitZero
        end
      end
    end.

Definition procInt (st : State) (tr : InternalTransition) (ts : Timestamp) :=
    let: Node n prs bf pool := st in
    match tr with
    | TxT tx => pair st (emitBroadcast n prs (TxMsg tx))

    (* Assumption: nodes broadcast to themselves as well! => simplifies logic *)
    | MintT =>
      let: bc := bfChain bf in
      let: allowedTxs := [seq t <- pool | txValid t bc] in
      match genProof n bc allowedTxs ts with
      | Some pf =>
        let: prevBlock := last GenesisBlock bc in
        let: block := mkB (hashB prevBlock) allowedTxs pf in
        if valid_chain_block bc block then
          let: newBf := bfExtend bf block in
          let: newPool := [seq t <- pool | txValid t (bfChain newBf)] in
          let: ownHashes := dom newBf ++ [seq hashT t | t <- newPool] in
          pair (Node n prs newBf newPool) (emitBroadcast n prs (BlockMsg block))
        else
          pair st emitZero
      | None => pair st emitZero
      end
    end.
