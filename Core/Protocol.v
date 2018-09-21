From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import Blockforest Node Casper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition StateMap := union_map [ordType of NodeId] State.

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
- case: validUn; rewrite ?validPt ?H2//.
  move=>k; rewrite domPt inE=>/eqP Z; subst k.
  by rewrite H1; move/negP: H_ni.
- move=>z; rewrite domUn !inE !domPt !inE.
  rewrite H1.
  case validUn.
  * by move/negP => H_v; case: H_v; rewrite validPt.
  * by move/negP.
  * move => k.
    rewrite H1.
    rewrite domPt inE=>/eqP H_eq.
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

Definition initState ps := initState' (enum NodeId) ps.

Definition PacketSoup := seq Packet.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

Definition holds (n : NodeId) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  [/\ valid (localState w),
     forall (n : NodeId),
       holds n w (fun st => id st == n),
     forall (n : NodeId),
       holds n w (fun st => valid (blocks st)),
     forall (n : NodeId),
       holds n w (fun st => validH (blocks st)),
     forall (n : NodeId),
       holds n w (fun st => has_init_block (blocks st)) &
     forall (n : NodeId),
       holds n w (fun st => uniq (peers st))
  ].

Record Qualifier := Q { ts: Timestamp; allowed: NodeId; }.

(* procInt currently undefined *)
(* Inductive system_step (w w' : World) (q : Qualifier) : Prop :=
| Idle of Coh w /\ w = w'

| Deliver (p : Packet) (st : State) of
      Coh w & (dst p) = allowed q &
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (src p) (msg p) (ts q) in
      w' = mkW (upd (dst p) st' (localState w))
               (seq.rem p (inFlightMsgs w) ++ ms)
               (rcons (consumedMsgs w) p)

| Intern (proc : NodeId) (t : InternalTransition) (st : State) of
      Coh w & proc = allowed q &
      find proc (localState w) = Some st &
      let: (st', ms) := (procInt st t (ts q)) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).
*)

Definition Schedule := seq Qualifier.

(* system_step currently undefined *)
(* Fixpoint reachable' (s : Schedule) (w w' : World) : Prop :=
  if s is (ins :: insts)
  then exists via, reachable' insts w via /\ system_step via w' ins
  else w = w'.
*)

(* reachable' currently undefined *)
(* Definition reachable (w w' : World) :=
  exists s, reachable' s w w'.
*)

Definition initWorld := mkW (initState (fun _ => enum NodeId)) [::] [::].

Ltac Coh_step_case n d H F :=
  case B: (n == d);
  do? [by move=>F; move: (H n _ F) |
    case: ifP; last done
  ]; move=>_ [] <-.

Lemma holds_Init_state : forall (P : State -> Prop) n ps, P (Init n (ps n)) ->
  holds n {| localState := initState ps; inFlightMsgs := [::]; consumedMsgs := [::] |} (fun st : State => P st).
Proof.
move => P n ps H_P; rewrite /initState.
have H_in: n \in enum NodeId by rewrite mem_enum.
have H_un: uniq (enum NodeId) by apply enum_uniq.
move: H_P H_in H_un; elim: (enum NodeId) => //=.
move => a s IH H_P; rewrite inE; move/orP; case.
* move/eqP => H_eq /=.
  rewrite H_eq; move/andP => [H_in H_u].
  rewrite /holds /= => st; rewrite findPtUn; first by case => H_i; rewrite -H_i -H_eq.
  by case: validUn; rewrite ?validPt ?valid_initState'//;
   move=>k; rewrite domPt !inE=>/eqP <-;
  rewrite dom_initState' //; move/negP: H_in.
* move => H_in; move/andP => [H_ni H_u].
  have H_neq: n <> a by move => H_eq; rewrite -H_eq in H_ni; move/negP: H_ni.
  move: H_in; move/IH {IH} => IH.
  have H_u' := H_u.
  move: H_u'; move/IH {IH}.
  rewrite /holds /= => IH st; rewrite findUnL.
  + case: ifP; last by move => H_in H_f; exact: IH.
    by rewrite domPt inE eq_sym; move/eqP.
  + by case: validUn; rewrite ?validPt ?valid_initState'//;
     move=>k; rewrite domPt !inE=>/eqP <-;
     rewrite dom_initState' //; move/negP: H_ni.
Qed.

Lemma Coh_init : Coh initWorld.
Proof.
rewrite /initWorld/localState/=; split.
- apply: valid_initState'.
  exact: enum_uniq.
- by move => n; exact: holds_Init_state.
- move => n; apply: holds_Init_state.
  by rewrite /blocks /= validPt.
- move => n; apply: holds_Init_state.
  rewrite/validH/blocks /= => h b H.
  by move: (findPt_inv H); elim=>->->.
- move => n; apply: holds_Init_state.
  by rewrite/has_init_block/blocks findPt.
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

(* procInt currently undefined *)
(* Lemma procInt_id_constant : forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    id s1 = id (procInt s1 t ts).1.
Proof.
case=> n1 p1 b1 t1 [] =>// ts; simpl.
case hP: genProof => //.
case tV: (valid_chain_block _ _)=>//.
Qed.
*)

Lemma procMsg_valid :
   forall (s1 : State) from (m : Message) (ts : Timestamp),
    valid (blocks s1) -> valid (blocks (procMsg s1 from  m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[b|||];
destruct s1; rewrite/procMsg/=; do?by [|move: (bfExtendV blocks b)=><-].
case:ifP => //=.
move/eqP => H_neq; case: ifP; move/eqP => //= H_eq H_v.
by case ohead.
Qed.

(* procInt currently undefined *)
(* Lemma procInt_valid :
  forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    valid (blocks s1) = valid (blocks (procInt s1 t ts).1).
Proof.
move=>s1 t ts.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: (genProof _); last done.
move=>Pf.
case tV: (valid_chain_block _ _)=>//.
by rewrite/Node.blocks/=; apply bfExtendV.
Qed.
*)

Lemma procMsg_validH :
   forall (s1 : State) from  (m : Message) (ts : Timestamp),
     valid (blocks s1) -> validH (blocks s1) ->
     validH (blocks (procMsg s1 from  m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[b|||];
destruct s1; rewrite/procMsg/=; do? by []; do? by case: ifP => //=.
- by move=>v vh; apply bfExtendH.
- move=>v vh; case: ifP => //=; move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

(* procInt currently undefined *)
(* Lemma procInt_validH :
   forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
     valid (blocks s1) -> validH (blocks s1) ->
     validH (blocks (procInt s1 t ts).1).
Proof.
move=>s1 t ts v vh.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: (genProof _); last done.
move=>Pf.
case tV: (valid_chain_block _ _)=>//.
by rewrite/Node.blocks/=; apply bfExtendH.
Qed.
*)

Lemma procMsg_has_init_block:
   forall (s1 : State) from (m : Message) (ts : Timestamp),
     valid (blocks s1) -> validH (blocks s1) ->
     has_init_block (blocks s1) ->
     has_init_block (blocks (procMsg s1 from m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[b|||];
destruct s1; rewrite/procMsg/=; do? by []; do? by case:ifP.
- by apply bfExtendIB.
- move=>v vh; case: ifP => //=; move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

(* procInt currently undefined *)
(* Lemma procInt_has_init_block :
   forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
     valid (blocks s1) -> validH (blocks s1) ->
     has_init_block (blocks s1) ->
     has_init_block (blocks (procInt s1 t ts).1).
Proof.
move=>s1 t ts v vh.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: (genProof _); last done.
move=>Pf.
case tV: (valid_chain_block _ _)=>//.
by apply bfExtendIB.
Qed.
*)

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

(* procInt currently undefined *)
(* Lemma procInt_peers_uniq :
  forall (s1 : State) (t : InternalTransition) ts, let: s2 := (procInt s1 t ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
move=>s1 t ts; case: s1=>n prs bf txp; rewrite /peers/procInt=>Up.
case: t=>//; case hP: (genProof _)=>//.
case tV: (valid_chain_block _ _)=>//.
Qed.
*)

(* most deifnitions in remainder of file rely on some combination of 
   system_step, reachable, etc. of which the definitions are currently
   commented out
*)

(*
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
  forall (n : NodeId) (st st' : State),
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

Lemma no_change_still_holds (w w' : World) (n : NodeId) q st cond:
  find n (localState w) = Some st ->
  holds n w cond ->
  system_step w w' q ->
  find n (localState w') = Some st ->
  holds n w' cond.
Proof.
move=>f h S sF st' s'F; rewrite s'F in sF; case: sF=>->.
by move: (h st f).
Qed.

Lemma no_change_has_held (w w' : World) (n : NodeId) q st cond:
  find n (localState w) = Some st ->
  system_step w w' q->
  holds n w' cond ->
  find n (localState w') = Some st ->
  holds n w cond.
Proof.
move=> f S h sF st' s'F.
by rewrite f in s'F; case: s'F=><-; move: (h st sF).
Qed.
*)