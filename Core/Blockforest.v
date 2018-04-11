From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype finset.
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
    proof : VProof
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

Parameter NodeId : finType.
Parameter Address : finType.

Definition ValidatorIndex := nat.
Definition Wei := nat.
Definition Epoch := nat.
Definition Dynasty := nat.

(* casper payload signature *)
Parameter Signature : eqType.

(* Deposit(VALIDATION_ADDR, WITHDRAWAL_ADDR, DEPOSIT) *)

Record Deposit :=
  mkDeposit {
   deposit_validation_addr : Address;
   deposit_withdrawal_addr : Address;
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

Inductive Sender :=
| NullSender : Sender
| AddrSender : Address -> Sender.

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

Definition block := @Block Hash [eqType of Transaction] VProof.

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

Definition Blockforest := union_map Hash block.

Definition TxPool := seq Transaction.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : NodeId -> Blockchain -> TxPool -> Timestamp -> option VProof.
Parameter VAF : VProof -> Timestamp -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.
Parameter blockNumber : block -> nat.

Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> Blockforest -> Transaction -> TxPool.

Parameter sigValid_epoch : Address -> ValidatorIndex -> Epoch -> Signature -> bool.
Parameter sigValid_epochs : Address -> ValidatorIndex -> Hash -> Epoch -> Epoch -> Signature -> bool.

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

Lemma btExtendV bt b : valid bt = valid (btExtend bt b).
Proof.
rewrite /btExtend; case: ifP=>//N.
by rewrite gen_validPtUn/= N andbC.
Qed.

Lemma btExtendH bt b : valid bt -> validH bt -> validH (btExtend bt b).
Proof.
move=>V H z c; rewrite /btExtend.
case: ifP=>X; first by move/H.
rewrite findUnL ?gen_validPtUn ?V ?X//.
case: ifP=>Y; last by move/H.
rewrite um_domPt inE in Y; move/eqP: Y=>Y; subst z.
by rewrite um_findPt; case=>->.
Qed.

Lemma btExtendIB bt b :
  valid bt -> validH bt -> has_init_block bt ->
  has_init_block (btExtend bt b).
Proof.
move=>V H; rewrite /btExtend/has_init_block=>Ib.
case: ifP=>X; first done.
rewrite findUnL ?gen_validPtUn ?V ?X//.
case: ifP=>Y; last done.
rewrite um_domPt inE in Y; move/eqP: Y=>Y.
by specialize (hashB_inj Y)=><-; rewrite Y um_findPt.
Qed.

Definition tx_valid_block bc (b : block) := all [pred t | txValid t bc] (txs b).

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
