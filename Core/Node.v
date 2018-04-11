From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype.
From mathcomp
Require Import path.
Require Import Eqdep Relations.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import Blockforest Casper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition NodeId_ordMixin := fin_ordMixin NodeId.
Canonical NodeId_ordType := Eval hnf in OrdType NodeId NodeId_ordMixin.

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
    blockTree : Blockforest;
    txPool : TxPool;
  }.

Definition Init (n : NodeId) (peers : seq NodeId) : State :=
  Node n peers (#GenesisBlock \\-> GenesisBlock) [::].

Definition procMsg (st: State) (from : NodeId) (msg: Message) (ts: Timestamp) :=
    let: Node n prs bt pool := st in
    match msg with
    | BlockMsg b =>
      let: newBt := btExtend bt b in
      let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
      let: ownHashes := (keys_of newBt) ++ [seq hashT t | t <- newPool] in
      pair (Node n prs newBt newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | TxMsg tx =>
      let: newPool := tpExtend pool bt tx in
      let: ownHashes := (keys_of bt) ++ [seq hashT t | t <- newPool] in
      pair (Node n prs bt newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | InvMsg peerHashes =>
      let: ownHashes := (keys_of bt) ++ [seq hashT t | t <- pool] in
      let: newH := [seq h <- peerHashes | h \notin ownHashes] in
      let: gets := [seq mkP n from (GetDataMsg h) | h <- newH] in
      pair st (emitMany gets)

    | GetDataMsg h =>
      (* Do not respond to yourself *)
      if from == n then pair st emitZero else
      let: matchingBlocks := [seq b <- [:: get_block bt h] | b != GenesisBlock] in
      match ohead matchingBlocks with
      | Some b => pair (Node n prs bt pool) (emitOne (mkP n from (BlockMsg b)))
      | None =>
        let: matchingTxs := [seq t <- pool | (hashT t) == h] in
        match ohead matchingTxs with
        | Some tx =>
          pair (Node n prs bt pool) (emitOne (mkP n from (TxMsg tx)))
        | None => pair st emitZero
        end
      end
    end.

Definition procInt (st : State) (tr : InternalTransition) (ts : Timestamp) :=
    let: Node n prs bt pool := st in
    match tr with
    | TxT tx => pair st (emitBroadcast n prs (TxMsg tx))

    (* Assumption: nodes broadcast to themselves as well! => simplifies logic *)
    | MintT =>
      let: bc := btChain bt in
      let: allowedTxs := [seq t <- pool | txValid t bc] in
      match genProof n bc allowedTxs ts with
      | Some pf =>
        if VAF pf ts bc allowedTxs then
          let: prevBlock := last GenesisBlock bc in
          let: block := mkB (hashB prevBlock) allowedTxs pf in
          if tx_valid_block bc block then
            let: newBt := btExtend bt block in
            let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
            let: ownHashes := (keys_of newBt) ++ [seq hashT t | t <- newPool] in
            pair (Node n prs newBt newPool) (emitBroadcast n prs (BlockMsg block))
          else
            pair st emitZero
        else
          pair st emitZero
      | None => pair st emitZero
      end
    end.

(* -----------------*)
(* CASPER FUNCTIONS *)
(* -----------------*)
