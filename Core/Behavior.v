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
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator /\ ~ sigValid_epoch validator.(validator_addr) l.(logout_validator_index) l.(logout_epoch) l.(logout_sig) /\
       st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator /\ validator.(validator_end_dynasty) <= st.(casper_current_dynasty) + casper_dynasty_logout_delay /\ 
       st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find l.(logout_validator_index) st.(casper_validators) = Some validator /\
       st' = {[st
         with casper_validators := l.(logout_validator_index) \\->
                                   {[validator
                                   with validator_end_dynasty := st.(casper_current_dynasty) +
                                                                 casper_dynasty_logout_delay]} \+
                                   st.(casper_validators)]} /\ sa = [::]) \/
    (s = NullSender /\
       st' = st /\ sa = [::]).
Proof.
  intros. unfold procContractCallTx, tx_call, tx_sender in H.

  (* Case match on sender. NullSender case is trivial. *)
  destruct s; first by repeat right; inversion H.

  (* Case match on existence of validator. Trivially discharge goal if no validator. *)
  destruct (find (logout_validator_index l) (casper_validators st));
    last by left; exists s; inversion H.

  (* Case match on boolean conditions of if statement in H. *)
  destruct (casper_current_epoch st == block_number %/ casper_epoch_length) eqn:H1.
  destruct (logout_epoch l <= casper_current_epoch st) eqn:H2.
  destruct (sigValid_epoch (validator_addr v) (logout_validator_index l)
                           (logout_epoch l) (logout_sig l)) eqn:H3.
  destruct (casper_current_dynasty st + casper_dynasty_logout_delay < validator_end_dynasty v)
           eqn:H4.

  (* all true case: st updated *)
  - do 5 right; left.
    exists s; split; auto. exists v; split; auto.
    by inversion H.

  (* current dynasty + logout_delay < end_dynasty = false *)
  - do 4 right; left. exists s; split; auto. exists v; split; auto. split.
    apply negbT in H4; rewrite leqNgt; auto.
    by inversion H.

  (* sigValid_epoch addr index epoch sig = false *)
  - do 3 right; left. exists s; split; auto. exists v; split. auto. split.
    move/negP in H3; auto.
    by inversion H.

  (* logout_epoch <= current_epoch = false *)
  - do 2 right; left. exists s; split; auto. exists v; split; auto. split.
    apply negbT in H2; rewrite ltnNge; auto.
    by inversion H.

  (* current_epoch == block_number / epoch_length = false *)
  - right; left. exists s; split; auto. exists v; split; auto. split; move/eqP in H1; auto.
    by inversion H.
Qed.

Lemma procContractCallTx_WithdrawCall :
  forall (s : Sender)(block_number : nat) (st st' : CasperData) (validator_index : ValidatorIndex) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (WithdrawCall validator_index)) st = (st', sa) ->
    (exists sender_addr, s = AddrSender sender_addr /\ find validator_index st.(casper_validators) = None /\
     st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator /\ find validator.(validator_end_dynasty).+1 st.(casper_dynasty_start_epoch) = None /\
     st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator /\ exists epoch, find validator.(validator_end_dynasty).+1 st.(casper_dynasty_start_epoch) = Some epoch /\ find epoch validator.(validator_deposit) = None /\
     st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator /\ exists epoch, find validator.(validator_end_dynasty).+1 st.(casper_dynasty_start_epoch) = Some epoch /\ exists deposit, find epoch validator.(validator_deposit) = Some deposit /\ st.(casper_current_dynasty) <= validator.(validator_end_dynasty) /\
     st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator /\ exists epoch, find validator.(validator_end_dynasty).+1 st.(casper_dynasty_start_epoch) = Some epoch /\ exists deposit, find epoch validator.(validator_deposit) = Some deposit /\ st.(casper_current_epoch) < epoch + casper_withdrawal_delay /\
     st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator (* more details here *)) \/
    (s = NullSender /\ st' = st /\ sa = [::]).
Proof.
  intros. unfold procContractCallTx, tx_call, tx_sender in H.

  (* Case match on sender. NullSender case is trivial. *)
  destruct s; first by repeat right; inversion H.

  (* Case match on existence of validator. Trivially discharge goal if no validator. *)
  destruct (find validator_index (casper_validators st));
    last by left; exists s; inversion H.

  (* Case match on existence of end epoch. Trivially discharge goal if no end epoch. *)
  destruct (find (validator_end_dynasty v).+1 (casper_dynasty_start_epoch st)) eqn:H';
    last by right; left; exists s; split; auto; exists v; inversion H; subst.

  (* Case match on existence of deposit. Trivially discharge goal if no deposit. *)
  destruct (find e (validator_deposit v)) eqn:H'';
    last by do 2 right; left; exists s; split; auto; exists v; split; auto;
      exists e; inversion H; subst.

  (* Case match on boolean conditions of if statement in H. *)
  destruct (validator_end_dynasty v < casper_current_dynasty st) eqn:H1.
  destruct (e + casper_withdrawal_delay <= casper_current_epoch st) eqn:H2.

  (* incomplete case: all true *)
  - by do 5 right; left; exists s; split; auto; exists v.

  (* epoch + casper_withdrawal_delay > casper_current_epoch *)
  - inversion H; subst.
    do 4 right; left. exists s; split; auto. exists v; split; auto.
    exists e; split; auto. exists w.
    by apply negbT in H2; rewrite leqNgt.

  (* validator_end_dynasty >= casper_current_dynasty *)
  - inversion H; subst.
    do 3 right; left. exists s; split; auto. exists v; split; auto.
    exists e; split; auto. exists w.
    by apply negbT in H1; rewrite leqNgt.
Qed.

Lemma procContractCallTx_DepositCall :
  forall (s : Sender) (block_number : nat) (st st' : CasperData) (d : Deposit) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (DepositCall d)) st = (st', sa) ->
    (exists sender_addr, s = AddrSender sender_addr /\ st.(casper_current_epoch) <> block_number %/ casper_epoch_length /\ st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr /\ d.(deposit_amount) < casper_min_deposit_size /\ st' = st /\ sa = [::]) \/
    (exists sender_addr, s = AddrSender sender_addr (* more details here *)) \/
    (s = NullSender /\ st' = st /\ sa = [::]).
Proof.
  intros. unfold procContractCallTx, tx_call, tx_sender in H.

  (* Case match on sender. NullSender case is trivial. *)
  destruct s; first by repeat right; inversion H.

  (* Case match on boolean conditions of if statement in H. *)
  destruct (casper_current_epoch st == block_number %/ casper_epoch_length) eqn:H1.
  destruct (casper_min_deposit_size <= deposit_amount d) eqn:H2.

  (* incomplete case: all true *)
  - by do 2 right; left; exists s.

  (* casper_min_deposit_size > deposit_amount *)
  - inversion H; subst.
    right; left. exists s; split; auto.
    by apply negbT in H2; rewrite leqNgt.

  (* current_epoch == block_number / epoch_length = false *)
  - inversion H; subst.
    left. exists s; split; auto.
    by move/eqP in H1.
Qed.

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
  intros. unfold procContractCallTx, tx_call, tx_sender in H.

  (* Case match on sender. NullSender case is trivial. *)
  destruct s; first by repeat right; inversion H.

  (* Case match on existence of validator. Trivially discharge goal if no validator. *)
  destruct (find (vote_validator_index v1) (casper_validators st));
    last by left; exists s; inversion H.

  (* Case match on existence of deposit. Trivially discharge goal if no deposit. *)
  destruct (find (casper_current_epoch st) (validator_deposit v)) eqn:H';
    last by inversion H; subst; right; left; exists s; auto; split; auto; exists v.

  (* Case match on boolean conditions of if statement in H. *)
  destruct (sigValid_epochs (validator_addr v) (vote_validator_index v1)
              (vote_target_hash v1) (vote_target_epoch v1) (vote_source_epoch v1)
              (vote_sig v1)) eqn:H1.
  destruct (sigValid_epochs (validator_addr v) (vote_validator_index v2)
              (vote_target_hash v2) (vote_target_epoch v2) (vote_source_epoch v2)
              (vote_sig v2)) eqn:H2.
  destruct (vote_validator_index v1 == vote_validator_index v2) eqn:H3.
  destruct ([&& vote_target_hash v1 == vote_target_hash v2,
                vote_target_epoch v1 == vote_target_epoch v2
                & vote_source_epoch v1 == vote_source_epoch v2]) eqn:H4.

  (* target_hash, tearget_epoch, source_epoch for v1/v2 equal *)
  - inversion H; subst.
    do 5 right; left. exists s; split; auto. exists v; split; auto. move/eqP in H3.
    move/andP in H4; inversion H4. move/andP in H5; inversion H5.
    by exists w; repeat split; auto; apply/eqP.

  (* not (target_hash, tearget_epoch, source_epoch for v1/v2 equal) *)
  - do 6 right. left. exists s; split; auto. exists v; split; auto. move/eqP in H3.

    destruct ([|| vote_target_epoch v1 == vote_target_epoch v2,
                  (vote_target_epoch v2 < vote_target_epoch v1) &&
                  (vote_source_epoch v1 < vote_source_epoch v2)
                | (vote_target_epoch v1 < vote_target_epoch v2) &&
                  (vote_source_epoch v2 < vote_source_epoch v1)]) eqn:H5.

    (* incomplete spec: all true *)
    * by admit.

    * inversion H; subst. exists w; repeat split; auto.
      move/and3P in H4. unfold not; intros.
      destruct H4; inversion H0; inversion H6; subst.
      move/eqP in H4; move/eqP in H7; move/eqP in H8.
      by repeat split.

  (* vote_validator_index v1 =/= vote_validator_index v2 *)
  - inversion H; subst.
    do 4 right; left. exists s; split; auto. exists v; split; auto. move/eqP in H3.
    by exists w; repeat split.

  (* sigValid_epochs ... v2 = false *)
  - inversion H; subst.
    do 3 right; left. exists s; split; auto. exists v; split; auto. move/negP in H2.
    by exists w; split.

  (* sigValid_epochs ... v1 = false *)
  - inversion H; subst.
    do 2 right; left. exists s; split; auto. exists v; split; auto. move/negP in H1.
    by exists w; split.

  Admitted.
