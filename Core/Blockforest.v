From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype.
From mathcomp
Require Import path.
Require Import Eqdep.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------ *)
(* BLOCKS *)
(* ------ *)

Record Block {Hash : ordType} {Transaction VProof : eqType} :=
  mkB {
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.

Definition eq_block {H : ordType} {T P : eqType} (b b' : @Block H T P) :=
  match b, b' with
  | mkB p t pf, mkB p' t' pf' =>
    [&& p == p', t == t' & pf == pf']
  end.
      
Lemma eq_blockP {H : ordType} {T P : eqType} : Equality.axiom (@eq_block H T P).
Proof.
case=> p t pf; case=> p' t' pf'; rewrite /eq_block/=.
case H2: (p == p'); [move/eqP: H2=>?; subst p'| constructor 2];
  last by case=>?; subst p';rewrite eqxx in H2.
case H3: (t == t'); [move/eqP: H3=>?; subst t'| constructor 2];
  last by case=>?; subst t';rewrite eqxx in H3.
case H4: (pf == pf'); [move/eqP: H4=>?; subst pf'| constructor 2];
  last by case=>?; subst pf';rewrite eqxx in H4.
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

(* ------- *)
(* FORESTS *)
(* ------- *)

Parameter Timestamp : Type.
Parameter Hash : ordType.

Parameter VProof : eqType.
Parameter Transaction : eqType.
Parameter Address : finType.

Definition block := @Block Hash Transaction VProof.

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

Definition Blockforest := union_map Hash block.

Definition TxPool := seq Transaction.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option VProof.
Parameter VAF : VProof -> Timestamp -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> Blockforest -> Transaction -> TxPool.

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).
Notation "# b" := (hashB b) (at level 20).

Axiom hashB_inj : injective hashB.

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition btHasBlock (bt : Blockforest) (b : block) := #b \in dom bt.

Notation "b ∈ bt" := (btHasBlock bt b) (at level 70).
Notation "b ∉ bt" := (~~ btHasBlock bt b) (at level 70).

Definition valid_block b : bool :=
  prevBlockHash b != #b.

Definition has_init_block (bt : Blockforest) :=
  find (# GenesisBlock) bt = Some GenesisBlock.

Definition validH (bt : Blockforest) :=
  forall h b, find h bt = Some b -> h = hashB b.

Lemma validH_free bt (b : block) :
  validH bt -> validH (free (# b) bt).
Proof. by move=>Vh h c; rewrite findF;case: ifP=>//_ /Vh. Qed.

(* We only add "fresh blocks" *)
Definition btExtend (bt : Blockforest) (b : block) :=
  if #b \in dom bt then bt else #b \\-> b \+ bt.

Definition tx_valid_block bc (b : block) := all [pred t | txValid t bc] (txs b).

Definition next_of (bt : Blockforest) b : pred Block :=
  [pred b' | (hashB b == prevBlockHash b') && (hashB b' \in dom bt)].

(* All paths/chains should start with the GenesisBlock *)
Fixpoint compute_chain' (bt : Blockforest) b remaining n : Blockchain :=
  (* Preventing cycles in chains *)
  if (hashB b) \in remaining
  then
    let rest := seq.rem (hashB b) remaining in
    (* Supporting primitive inductions *)
    if n is n'.+1 then
      match find (prevBlockHash b) bt with
      (* No parent *)
      | None => [:: b]
      (* Build chain prefix recursively *)
      | Some prev =>
        rcons (nosimpl (compute_chain' (free (hashB b) bt) prev rest n')) b
      end
    else [::]
  else [::].

(* Compute chain from the block *)
Definition compute_chain bt b :=
  compute_chain' bt b (keys_of bt) (size (keys_of bt)).

(* Total get_block function *)
Definition get_block (bt : Blockforest) k : Block :=
  if find k bt is Some b then b else GenesisBlock.

(* Collect all blocks *)
Definition all_blocks (bt : Blockforest) := [seq get_block bt k | k <- keys_of bt].

Definition is_block_in (bt : Blockforest) b := exists k, find k bt = Some b.

(* A certificate for all_blocks *)
Lemma all_blocksP bt b : reflect (is_block_in bt b) (b \in all_blocks bt).
Proof.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  rewrite keys_dom in Ik; move/gen_eta: Ik=>[b]/=[E H].
  by exists k; rewrite /get_block E.
case=>k F; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists k; last by rewrite /get_block F.
by rewrite keys_dom; move/find_some: F.
Qed.

Lemma all_blocksP' bt b : validH bt -> reflect (b ∈ bt) (b \in all_blocks bt).
Proof.
move=>Vh.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  rewrite keys_dom in Ik; move/gen_eta: Ik=>[b]/=[E H].
  rewrite/get_block E /btHasBlock; specialize (Vh _ _ E); subst k.
  by move: (find_some E).
case=>H; rewrite/btHasBlock; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists (#b); first by rewrite keys_dom.
rewrite/btHasBlock in H; rewrite/get_block.
case X: (find _ _)=>[b'|].
by move: (Vh _  _ X); move/hashB_inj.
by contradict H; move: (find_none X)=>H; apply/negP.
Qed.

(* All chains from the given tree *)
Definition good_chain (bc : Blockchain) :=
  if bc is h :: _ then h == GenesisBlock else false.

(* Transaction validity *)
Fixpoint tx_valid_chain' (bc prefix : seq block) :=
  if bc is b :: bc'
  then [&& all [pred t | txValid t prefix] (txs b) &
        tx_valid_chain' bc' (rcons prefix b)]
  else true.
           
Definition tx_valid_chain bc := tx_valid_chain' bc [::].

Definition all_chains bt := [seq compute_chain bt b | b <- all_blocks bt].

Definition good_chains bt := [seq c <- all_chains bt | good_chain c && tx_valid_chain c].

(* Get the blockchain *)
Definition take_better_bc bc2 bc1 :=
  if (good_chain bc2 && tx_valid_chain bc2) && (bc2 > bc1) then bc2 else bc1.

Definition btChain bt : Blockchain :=
  foldr take_better_bc [:: GenesisBlock] (all_chains bt).
