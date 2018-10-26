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

Parameter Validator : finType.

Record Attestation {Hash : ordType} :=
  mkAR {
    view_src : nat;
    attester : Validator;
  }.

Definition eq_attestation {Hash : ordType} (ar ar' : @Attestation Hash) :=
match ar, ar' with
| mkAR v1 a1, mkAR v2 a2 => (v1 == v2) && (a1 == a2)
end.

Lemma eq_attestationP {Hash : ordType} : Equality.axiom (@eq_attestation Hash).
Proof.
case => v1 a1; case => v2 a2.
case H2: (v1 == v2); last first.
  rewrite /= H2; constructor; case.
  by move/eqP: H2.
case H3: (a1 == a2); last first.
  rewrite /= H2 H3; constructor; case.
  by move/eqP: H3.
rewrite /= H2 H3; constructor.
move/eqP: H2=>->.
by move/eqP: H3=>->.
Qed.

Definition Attestation_eqMixin {Hash : ordType} :=
 EqMixin (@eq_attestationP Hash).
Canonical Attestation_eqType {Hash : ordType} :=
 Eval hnf in EqType (@Attestation Hash) (@Attestation_eqMixin Hash).
  
Record Block {Hash : ordType} :=
  mkB {
    parent_hash : Hash;      
    block_view : nat;
    attestations : seq (@Attestation Hash);
  }.

Definition eq_block {Hash : ordType} (b b' : @Block Hash) :=
match b, b' with
| mkB ph bv att, mkB ph' bv' att' =>
  [&& ph == ph', bv == bv' & att == att']
end.

Lemma eq_blockP {Hash : ordType} : Equality.axiom (@eq_block Hash).
Proof.
case => ph bv att; case => ph' bv' att'.
rewrite /eq_block/=.
case H2: (ph == ph'); [move/eqP: H2=>?; subst ph'| constructor 2];
  last by case=>?; subst ph';rewrite eqxx in H2.
case H3: (bv == bv'); [move/eqP: H3=>?; subst bv'| constructor 2];
  last by case=>?; subst bv';rewrite eqxx in H3.
case H4: (att == att'); [move/eqP: H4=>?; subst att'| constructor 2];
  last by case=>?; subst att';rewrite eqxx in H4.
by constructor. 
Qed.

Definition Block_eqMixin {Hash : ordType} :=
 EqMixin (@eq_blockP Hash).
Canonical Block_eqType {Hash : ordType} :=
 Eval hnf in EqType (@Block Hash) (@Block_eqMixin Hash).
  
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

(* --------------*)
(* BLOCK FORESTS *)
(* --------------*)

Parameter Hash : finType.

Definition Hash_ordMixin := fin_ordMixin Hash.
Canonical Hash_finType := Eval hnf in OrdType Hash Hash_ordMixin.

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
