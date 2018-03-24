From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype.
From mathcomp
Require Import path.
Require Import Eqdep Relations.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import Blockforest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------*)
(* PROTOCOL MESSAGES *)
(* ------------------*)

Definition peers_t := seq Address.

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

Record Packet := mkP {src: Address; dst: Address; msg: Message}.

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

Definition emitBroadcast (from : Address) (dst : seq Address) (msg : Message) :=
  [seq (mkP from to msg) | to <- dst].

(* ------------------*)
(* NODE STATE & CODE *)
(* ------------------*)

Record State :=
  Node {
    id : Address;
    peers : peers_t;
    blockTree : Blockforest;
    txPool : TxPool;
  }.

Definition Init (n : Address) (peers : seq Address) : State :=
  Node n peers (#GenesisBlock \\-> GenesisBlock) [::].

Definition procMsg (st: State) (from : Address) (msg: Message) (ts: Timestamp) :=
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

Definition StateMap := union_map [ordType of Address] State.

Definition initState' s ps : StateMap := foldr (fun a m => (a \\-> Init a (ps a)) \+ m) Unit s.

(* Master-lemma, proving a conjunction of two mutually-necessary facts *)
Lemma initStateValidDom s ps :
  uniq s -> dom (initState' s ps) =i s /\ valid (initState' s ps).
Proof.
elim: s => /=[|a s']; first by rewrite valid_unit dom0.
move => IH.
move/andP => [H_ni H_u].
move/IH: H_u => [H1 H2] {IH}.
split; last first.
- case: validUn; rewrite ?um_validPt ?H2//.
  move=>k; rewrite um_domPt inE=>/eqP Z; subst k.
  rewrite H1.
  by move/negP: H_ni.
- move=>z; rewrite domUn !inE !um_domPt !inE.
  rewrite H1.
  case validUn.
  * by move/negP => H_v; case: H_v; rewrite um_validPt.
  * by move/negP.
  * move => k.
    rewrite H1.
    rewrite um_domPt inE=>/eqP H_eq.
    rewrite -H_eq => H_in.
    by move/negP: H_ni.
  * move => Hv1 Hv2 H_d.
    by rewrite eq_sym.
Qed.

Lemma valid_initState' s ps : uniq s -> valid (initState' s ps).
Proof. by move => H_u; case: (initStateValidDom ps H_u). Qed.

Lemma dom_initState' s ps : uniq s -> dom (initState' s ps) =i s.
Proof. by move => H_u; case: (initStateValidDom ps H_u). Qed.

(* ------------------*)
(* TRANSITION SYSTEM *)
(* ------------------*)

Definition initState ps := initState' (enum Address) ps.

Definition PacketSoup := seq Packet.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

Definition holds (n : Address) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  [/\ valid (localState w),
     forall (n : Address),
       holds n w (fun st => id st == n),
     forall (n : Address),
       holds n w (fun st => valid (blockTree st)),
     forall (n : Address),
       holds n w (fun st => validH (blockTree st)),
     forall (n : Address),
       holds n w (fun st => has_init_block (blockTree st)) &
     forall (n : Address),
       holds n w (fun st => uniq (peers st))
  ].

Record Qualifier := Q { ts: Timestamp; allowed: Address; }.

(* Don't you worry about uniqueness of the messages? *)
Inductive system_step (w w' : World) (q : Qualifier) : Prop :=
| Idle of Coh w /\ w = w'

| Deliver (p : Packet) (st : State) of
      Coh w & (dst p) = allowed q &
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (src p) (msg p) (ts q) in
      w' = mkW (upd (dst p) st' (localState w))
               (seq.rem p (inFlightMsgs w) ++ ms)
               (rcons (consumedMsgs w) p)

| Intern (proc : Address) (t : InternalTransition) (st : State) of
      Coh w & proc = allowed q &
      find proc (localState w) = Some st &
      let: (st', ms) := (procInt st t (ts q)) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition Schedule := seq Qualifier.

Fixpoint reachable' (s : Schedule) (w w' : World) : Prop :=
  if s is (ins :: insts)
  then exists via, reachable' insts w via /\ system_step via w' ins
  else w = w'.

Definition reachable (w w' : World) :=
  exists s, reachable' s w w'.

Definition initWorld := mkW (initState (fun _ => enum Address)) [::] [::].

Ltac Coh_step_case n d H F :=
  case B: (n == d);
  do? [by move=>F; move: (H n _ F) |
    case: ifP; last done
  ]; move=>_ [] <-.

Lemma holds_Init_state : forall (P : State -> Prop) n ps, P (Init n (ps n)) ->
  holds n {| localState := initState ps; inFlightMsgs := [::]; consumedMsgs := [::] |} (fun st : State => P st).
Proof.
move => P n ps H_P; rewrite /initState.
have H_in: n \in enum Address by rewrite mem_enum.
have H_un: uniq (enum Address) by apply enum_uniq.
move: H_P H_in H_un; elim: (enum Address) => //=.
move => a s IH H_P; rewrite inE; move/orP; case.
* move/eqP => H_eq /=.
  rewrite H_eq; move/andP => [H_in H_u].
  rewrite /holds /= => st; rewrite gen_findPtUn; first by case => H_i; rewrite -H_i -H_eq.
  by case: validUn; rewrite ?um_validPt ?valid_initState'//;
   move=>k; rewrite um_domPt !inE=>/eqP <-;
  rewrite dom_initState' //; move/negP: H_in.
* move => H_in; move/andP => [H_ni H_u].
  have H_neq: n <> a by move => H_eq; rewrite -H_eq in H_ni; move/negP: H_ni.
  move: H_in; move/IH {IH} => IH.
  have H_u' := H_u.
  move: H_u'; move/IH {IH}.
  rewrite /holds /= => IH st; rewrite findUnL.
  + case: ifP; last by move => H_in H_f; exact: IH.
    by rewrite um_domPt inE eq_sym; move/eqP.
  + by case: validUn; rewrite ?um_validPt ?valid_initState'//;
     move=>k; rewrite um_domPt !inE=>/eqP <-;
     rewrite dom_initState' //; move/negP: H_ni.
Qed.

Lemma Coh_init : Coh initWorld.
Proof.
rewrite /initWorld/localState/=; split.
- apply: valid_initState'.
  exact: enum_uniq.
- by move => n; exact: holds_Init_state.
- move => n; apply: holds_Init_state.
  by rewrite /blockTree /= um_validPt.
- move => n; apply: holds_Init_state.
  rewrite/validH/blockTree /= => h b H.
  by move: (um_findPt_inv H); elim=>->->.
- move => n; apply: holds_Init_state.
  by rewrite/has_init_block/blockTree um_findPt.
- move => n; apply: holds_Init_state.
  exact: enum_uniq.
Qed.

Lemma procMsg_id_constant (s1 : State) from (m : Message) (ts : Timestamp) :
    id s1 = id (procMsg s1 from m ts).1.
Proof.
case: s1 from m ts=>n1 p1 b1 t1 from []=>//=??; case:ifP => //=.
move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
by case ohead.
Qed.

Lemma procInt_id_constant : forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    id s1 = id (procInt s1 t ts).1.
Proof.
case=> n1 p1 b1 t1 [] =>// ts; simpl.
case hP: genProof => //; case vP: (VAF _)=>//.
case tV: (tx_valid_block _ _)=>//.
Qed.

Lemma procMsg_valid :
   forall (s1 : State) from (m : Message) (ts : Timestamp),
    valid (blockTree s1) -> valid (blockTree (procMsg s1 from  m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[b|||];
destruct s1; rewrite/procMsg/=; do?by [|move: (btExtendV blockTree0 b)=><-].
case:ifP => //=.
move/eqP => H_neq; case: ifP; move/eqP => //= H_eq H_v.
by case ohead.
Qed.

Lemma procInt_valid :
  forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    valid (blockTree s1) = valid (blockTree (procInt s1 t ts).1).
Proof.
move=>s1 t ts.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: (genProof _); last done.
move=>Pf; case: (VAF _ _ _); last done.
case tV: (tx_valid_block _ _)=>//.
by rewrite/blockTree/=; apply btExtendV.
Qed.

Lemma procMsg_validH :
   forall (s1 : State) from  (m : Message) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     validH (blockTree (procMsg s1 from  m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[b|||];
destruct s1; rewrite/procMsg/=; do? by []; do? by case: ifP => //=.
- by move=>v vh; apply btExtendH.
- move=>v vh; case: ifP => //=; move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

Lemma procInt_validH :
   forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     validH (blockTree (procInt s1 t ts).1).
Proof.
move=>s1 t ts v vh.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: (genProof _); last done.
move=>Pf; case: (VAF _ _ _); last done.
case tV: (tx_valid_block _ _)=>//.
by rewrite/blockTree/=; apply btExtendH.
Qed.

Lemma procMsg_has_init_block:
   forall (s1 : State) from (m : Message) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     has_init_block (blockTree s1) ->
     has_init_block (blockTree (procMsg s1 from m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[b|||];
destruct s1; rewrite/procMsg/=; do? by []; do? by case:ifP.
- by apply btExtendIB.
- move=>v vh; case: ifP => //=; move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

Lemma procInt_has_init_block :
   forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     has_init_block (blockTree s1) ->
     has_init_block (blockTree (procInt s1 t ts).1).
Proof.
move=>s1 t ts v vh.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: (genProof _); last done.
move=>Pf; case: (VAF _ _ _); last done.
case tV: (tx_valid_block _ _)=>//.
by apply btExtendIB.
Qed.

Lemma procMsg_peers_uniq :
  forall (s1 : State) from  (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 from m ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
case=> n1 p1 b1 t1 from; case; do? by []; simpl.
move=>s _ U; case: ifP => //=.
move/eqP => H_eq; case: ifP; move/eqP => //= H_eq'.
by case ohead.
Qed.

Lemma procInt_peers_uniq :
  forall (s1 : State) (t : InternalTransition) ts, let: s2 := (procInt s1 t ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
move=>s1 t ts; case: s1=>n prs bt txp; rewrite /peers/procInt=>Up.
case: t=>//; case hP: (genProof _)=>//; case vP: (VAF _)=>//.
case tV: (tx_valid_block _ _)=>//.
Qed.

Lemma Coh_step w w' q:
  system_step w w' q -> Coh w'.
Proof.
move=>S; (have: system_step w w' q by done)=>S'.
case: S'.
(* Idle *)
by case=>Cw <-.
(* Deliver *)
- move=> p st [H1 H2 H3 H4 H5 H6] _ iF sF; case P: (procMsg _ _ _)=>[st' ms].
  move=>->; split;
    do? [rewrite /holds/localState; move=> n stN; rewrite findU=>/=].
  + rewrite /localState validU=>/=; apply H1.
  + Coh_step_case n (dst p) H2 F; move/eqP: (H2 (dst p) _ sF)=>Id.
    move: (procMsg_id_constant st (src p) (msg p) (ts q)).
    by move/eqP in B; subst n; rewrite Id=>->; rewrite P.
  + Coh_step_case n (dst p) H3 F; move: (H3 (dst p) _ sF)=>V.
    by move: (procMsg_valid (src p) (msg p) (ts q) V); rewrite P.
  + Coh_step_case n (dst p) H4 F;
    move: (H3 (dst p) _ sF)=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
    by apply procMsg_validH.
  + Coh_step_case n (dst p) H5 F.
    move: (H3 (dst p) _ sF)=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _;
    by move: (H5 (dst p) _ sF); apply procMsg_has_init_block.
  + Coh_step_case n (dst p) H6 F.
    move: (H3 (dst p) _ sF)=>V; move: (H4 (dst p) _ sF)=>VH;
    rewrite [procMsg _ _ _ _] surjective_pairing in P; case: P=><- _.
    by move: (H6 (dst p) _ sF); apply procMsg_peers_uniq.

(* Intern *)
- move=> proc t st [H1 H2 H3 H4 H5 H6] _ sF. case P: (procInt _ _ _)=>[st' ms].
  move=>->; split;
    do? [rewrite /holds/localState; move=> n stN; rewrite findU=>/=].
  + rewrite /localState validU=>/=; apply H1.
  + Coh_step_case n proc H2 F; move/eqP: (H2 proc _ sF)=>Id.
    move: (procInt_id_constant st t (ts q)).
    by move/eqP in B; subst n; rewrite Id=>->; rewrite P.
  + Coh_step_case n proc H3 F; move: (H3 proc _ sF)=>V.
    by move: (procInt_valid st t (ts q)); rewrite P/==><-.
  + Coh_step_case n proc H4 F;
    move: (H3 proc _ sF)=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=><- _;
    by apply procInt_validH.
  + Coh_step_case n proc H5 F.
    move: (H3 proc _ sF)=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=><- _;
    by move: (H5 proc _ sF); apply procInt_has_init_block.
  + Coh_step_case n proc H6 F.
    move: (H3 proc _ sF)=>V; move: (H4 proc _ sF)=>VH;
    rewrite [procInt _ _ _] surjective_pairing in P; case: P=><- _.
    by move: (H6 proc _ sF); apply procInt_peers_uniq.
Qed.

(* Stepping does not remove or add nodes *)
Lemma step_nodes w w' q :
  system_step w w' q ->
  dom (localState w) =i dom (localState w').
Proof.
case: w w'=>sm f c [sm'] f' c'; case=>/=; first by case=>C; case=>->/=.
- move=>p st1 C iq pf F; case: (procMsg st1 (src p) (msg p))=>st2 ms[]->{sm'}Z1 Z2.
  subst f' c'=>z; rewrite domU inE/=; case: ifP=>///eqP->{z}.
  by move/find_some: F->; case: C.
move=>p t st1 C iq F; case: (procInt st1 t)=>st2 ms[]->{sm'}Z1 Z2.
subst f' c'=>z; rewrite domU inE/=; case: ifP=>///eqP->{z}.
by move/find_some: F->; case: C.
Qed.

Lemma steps_nodes (w w' : World):
  reachable w w' ->
  dom (localState w) =i dom (localState w').
Proof.
move=>[sch] R. elim: sch w' R=>/=[w'->|q qs Hi w' [via] [R S]]//z.
by move: (Hi via R)->; rewrite (step_nodes S).
Qed.

Inductive local_step (s1 s2 : State) : Prop :=
| IdleStep of s1 = s2
| RcvMsgStep f m ts of (s2 = (procMsg s1 f m ts).1)
| IntTStep t ts of (s2 = (procInt s1 t ts).1).

Lemma system_step_local_step w w' q:
  forall (n : Address) (st st' : State),
    system_step w w' q ->
    find n (localState w) = Some st ->
    find n (localState w') = Some st' ->
    local_step st st'.
Proof.
move=> n st st'.
case.
(* Idle *)
- by move=>[] cW<-->[]->; constructor 1.
(* Deliver *)
- move=> p old_st cW _ pIF osF.
  case P: (procMsg _ _ _). case: w'. move=> sm' f' c'. case.
  move=> A B C. subst sm' f' c'. move=> sF. rewrite /localState findU=>/=.
  case B: (n == dst p); last first.
    (* n != dst p -- node n is Idle => st st' *)
    + move=> F. rewrite F in sF. case: sF=>stEq. rewrite stEq. by constructor 1.
    (* When n == dst p, notice that st = old_st
     * and st and st' are related by procMsg *)
    + move/eqP in B. rewrite -B in osF. rewrite sF in osF. case: osF=>->.
      case: ifP; last first.
        by move=> _ con; contradict con.
        move=> _ sEq. case: sEq=>stEq. rewrite stEq in P.
        by constructor 2 with (src p) (msg p) (ts q); rewrite P.
(* Intern *)
- move=> proc t old_st cW _ osF.
  case P: (procInt _ _ _). case: w'. move=> sm' f' c'. case.
  move=> A B C. subst sm' f' c'. move=> sF. rewrite /localState findU=>/=.
  case B: (n == proc); last first.
    (* n != proc -- node n is Idle => st st' *)
    + move=> F. rewrite F in sF. case: sF=>stEq. rewrite stEq. by constructor 1.
    (* n == proc => update; akin to Deliver *)
    + move/eqP in B. rewrite -B in osF. rewrite sF in osF. case: osF.
      move=> stEq. rewrite -stEq in P. clear stEq old_st.
      case: ifP; last first.
        by move=> _ con; contradict con.
        move=> _ sEq. case: sEq=> stEq. rewrite stEq in P.
        by constructor 3 with t (ts q); rewrite P.
Qed.

Lemma no_change_still_holds (w w' : World) (n : Address) q st cond:
  find n (localState w) = Some st ->
  holds n w cond ->
  system_step w w' q ->
  find n (localState w') = Some st ->
  holds n w' cond.
Proof.
move=>f h S sF st' s'F; rewrite s'F in sF; case: sF=>->.
by move: (h st f).
Qed.

Lemma no_change_has_held (w w' : World) (n : Address) q st cond:
  find n (localState w) = Some st ->
  system_step w w' q->
  holds n w' cond ->
  find n (localState w') = Some st ->
  holds n w cond.
Proof.
move=> f S h sF st' s'F.
by rewrite f in s'F; case: s'F=><-; move: (h st sF).
Qed.
