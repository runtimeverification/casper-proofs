From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype div path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From CasperToychain
Require Import Blockforest Casper Node.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma procContractCallTx_LogoutCall :
  forall (s : Sender) (block_number : nat) (st st' : CasperData) (l : Logout) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (LogoutCall l)) st = (st', sa) ->
    (exists sender_addr, s = AddrSender sender_addr /\ find l.(logout_validator_index) st.(casper_validators) = None /\
       st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator /\ st.(casper_current_epoch) <> block_number %/ casper_epoch_length /\
       st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator /\ st.(casper_current_epoch) < l.(logout_epoch) /\      
       st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator /\ validator.(validator_end_dynasty) <= st.(casper_current_dynasty) + casper_dynasty_logout_delay /\ 
       st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator (* more details here *)) \/
    (s = NullSender /\
       st' = st /\ sa = [::]).
Proof.
  intros.
  unfold procContractCallTx, tx_call, tx_sender in H.
  destruct s. repeat right; inversion H; auto.
  destruct (find (logout_validator_index l) (casper_validators st)) eqn:H'.
  destruct (casper_current_epoch st == block_number %/ casper_epoch_length) eqn:H1.
  destruct (logout_epoch l <= casper_current_epoch st) eqn:H2.
  destruct (sigValid_epoch (validator_addr v) (logout_validator_index l)
                           (logout_epoch l) (logout_sig l)) eqn:H3.
  destruct (casper_current_dynasty st + casper_dynasty_logout_delay < validator_end_dynasty v)
           eqn:H4.

  (* Incomplete case: all true *)
  - do 4 right; left. exists s; split; auto; exists v; auto.

  (* current dynasty + logout_delay < end_dynasty = false *)
  - do 3 right; left. exists s; split; auto. exists v; split; auto. split.
    apply negbT in H4; rewrite leqNgt; auto. inversion H; auto.

  (* Incomplete case: sigValid_epoch ... = false *)
  - do 4 right; left. exists s; split; auto; exists v; auto.

  (* logout_epoch <= current_epoch = false *)
  - do 2 right; left. exists s; split; auto. exists v; split; auto. split.
    apply negbT in H2; rewrite ltnNge; auto. inversion H; auto.

  (* current_epoch == block_number / epoch_length = false *)
  - right; left. exists s; split; auto. exists v; split; auto. split; move/eqP in H1; auto.
    inversion H; auto.

  (* sender = None *)
  - left; exists s; inversion H; auto.
Qed.

Lemma procContractCallTx_WithdrawCall :
  forall (s : Sender)(block_number : nat) (st st' : CasperData) (validator_index : ValidatorIndex) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (WithdrawCall validator_index)) st = (st', sa) ->
    (exists sender_addr, s = AddrSender sender_addr /\ find validator_index st.(casper_validators) = None /\
     st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator (* more details here *)) \/
    (s = NullSender /\ st' = st /\ sa = [::]).
Proof.
Admitted.

Lemma procContractCallTx_DepositCall :
  forall (s : Sender) (block_number : nat) (st st' : CasperData) (d : Deposit) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (DepositCall d)) st = (st', sa) ->
    (exists sender_addr, s = AddrSender sender_addr /\ st.(casper_current_epoch) <> block_number %/ casper_epoch_length /\ st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr (* more details here *)) \/
    (s = NullSender /\ st' = st /\ sa = [::]).
Proof.
Admitted.

Lemma procContractCallTx_SlashCall :
  forall (s : Sender) (block_number : nat) (st st' : CasperData) (v1 v2 : Vote) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (SlashCall v1 v2)) st = (st', sa) ->
    (exists sender_addr, s = AddrSender sender_addr /\ find v1.(vote_validator_index) st.(casper_validators) = None /\
      st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
      find st.(casper_current_epoch) validator.(validator_deposit) = None /\ 
      st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
      exists deposit, find st.(casper_current_epoch) validator.(validator_deposit) = Some deposit /\
      ~ sigValid_epochs validator.(validator_addr) v1.(vote_validator_index) v1.(vote_target_hash) v1.(vote_target_epoch) v1.(vote_source_epoch) v1.(vote_sig) /\
      st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
       exists deposit, find st.(casper_current_epoch) validator.(validator_deposit) = Some deposit /\
        ~ sigValid_epochs validator.(validator_addr) v2.(vote_validator_index) v2.(vote_target_hash) v2.(vote_target_epoch) v2.(vote_source_epoch) v2.(vote_sig) /\
        st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
       exists deposit, find st.(casper_current_epoch) validator.(validator_deposit) = Some deposit /\
        sigValid_epochs validator.(validator_addr) v1.(vote_validator_index) v1.(vote_target_hash) v1.(vote_target_epoch) v1.(vote_source_epoch) v1.(vote_sig) /\
        sigValid_epochs validator.(validator_addr) v2.(vote_validator_index) v2.(vote_target_hash) v2.(vote_target_epoch) v2.(vote_source_epoch) v2.(vote_sig) /\
        v1.(vote_validator_index) <> v2.(vote_validator_index) /\
        st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
       exists deposit, find st.(casper_current_epoch) validator.(validator_deposit) = Some deposit /\
        sigValid_epochs validator.(validator_addr) v1.(vote_validator_index) v1.(vote_target_hash) v1.(vote_target_epoch) v1.(vote_source_epoch) v1.(vote_sig) /\
        sigValid_epochs validator.(validator_addr) v2.(vote_validator_index) v2.(vote_target_hash) v2.(vote_target_epoch) v2.(vote_source_epoch) v2.(vote_sig) /\
        v1.(vote_validator_index) = v2.(vote_validator_index) /\
        v1.(vote_target_hash) = v2.(vote_target_hash) /\ v1.(vote_target_epoch) = v2.(vote_target_epoch) /\ v1.(vote_source_epoch) = v2.(vote_source_epoch) /\
        st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
       exists deposit, find st.(casper_current_epoch) validator.(validator_deposit) = Some deposit /\
        sigValid_epochs validator.(validator_addr) v1.(vote_validator_index) v1.(vote_target_hash) v1.(vote_target_epoch) v1.(vote_source_epoch) v1.(vote_sig) /\
        sigValid_epochs validator.(validator_addr) v2.(vote_validator_index) v2.(vote_target_hash) v2.(vote_target_epoch) v2.(vote_source_epoch) v2.(vote_sig) /\
        v1.(vote_validator_index) = v2.(vote_validator_index) /\
        ~ (v1.(vote_target_hash) = v2.(vote_target_hash) /\ v1.(vote_target_epoch) = v2.(vote_target_epoch) /\ v1.(vote_source_epoch) = v2.(vote_source_epoch)) /\
        st' = st /\ sa = [::]) \/
    (s = NullSender /\ st' = st /\ sa = [::]).
Proof.
Admitted.
