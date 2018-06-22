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
                                   st.(casper_validators)]} /\ sa = [::]
    /\ st.(casper_current_epoch) == block_number %/ casper_epoch_length
    /\ l.(logout_epoch) <= st.(casper_current_epoch)
    /\ sigValid_epoch validator.(validator_addr) l.(logout_validator_index) l.(logout_epoch) l.(logout_sig)
    /\ st.(casper_current_dynasty) + casper_dynasty_logout_delay < validator.(validator_end_dynasty)) \/
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
    (exists sender_addr, s = AddrSender sender_addr /\ exists validator, find validator_index st.(casper_validators) = Some validator /\ exists epoch, find validator.(validator_end_dynasty).+1 st.(casper_dynasty_start_epoch) = Some epoch /\ exists deposit, find epoch validator.(validator_deposit) = Some deposit /\
    st' = {[st
      with casper_validators := deleteValidator validator_index st.(casper_validators)]} /\
    sa = [:: {| send_account_addr := validator_withdrawal_addr validator; send_account_wei := deposit |}]
    /\ validator.(validator_end_dynasty) < st.(casper_current_dynasty)
    /\ epoch + casper_withdrawal_delay <= st.(casper_current_epoch)) \/
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

  (* all true case: st, sa updated *)
  - do 5 right; left. exists s; split; auto. exists v; split; auto.
    exists e; split; auto. exists w.
    by inversion H.

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
    (exists sender_addr, s = AddrSender sender_addr /\
      st' = {[{[st
        with casper_validators := casper_next_validator_index st \\->
                                  {|
                                  validator_addr := d.(deposit_validation_addr);
                                  validator_withdrawal_addr := d.(deposit_withdrawal_addr);
                                  validator_deposit := st.(casper_current_dynasty) \\->
                                                       d.(deposit_amount);
                                  validator_start_dynasty := st.(casper_current_epoch).+2;
                                  validator_end_dynasty := casper_default_end_dynasty |} \+
                                  st.(casper_validators)]}
              with casper_next_validator_index := st.(casper_next_validator_index).+1]}
      /\ sa = [::]
      /\ st.(casper_current_epoch) == block_number %/ casper_epoch_length
      /\ casper_min_deposit_size <= d.(deposit_amount)) \/
    (s = NullSender /\ st' = st /\ sa = [::]).
Proof.
  intros. unfold procContractCallTx, tx_call, tx_sender in H.

  (* Case match on sender. NullSender case is trivial. *)
  destruct s; first by repeat right; inversion H.

  (* Case match on boolean conditions of if statement in H. *)
  destruct (casper_current_epoch st == block_number %/ casper_epoch_length) eqn:H1.
  destruct (casper_min_deposit_size <= deposit_amount d) eqn:H2.

  (* all true case: st updated *)
  - do 2 right; left.
    exists s; split; auto.
    by inversion H.

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
    (exists sender_addr, s = AddrSender sender_addr /\
      exists validator, find v1.(vote_validator_index) st.(casper_validators) = Some validator /\
       exists deposit, find st.(casper_current_epoch) validator.(validator_deposit) = Some deposit /\
         st' = {[st
           with casper_validators := deleteValidator v1.(vote_validator_index)
                                      st.(casper_validators)]} /\
         sa = [:: {| send_account_addr := s; send_account_wei := deposit |}]
    /\ sigValid_epochs validator.(validator_addr)
         v1.(vote_validator_index) v1.(vote_target_hash)
         v1.(vote_target_epoch) v1.(vote_source_epoch)
         v1.(vote_sig)
    /\ sigValid_epochs validator.(validator_addr)
         v2.(vote_validator_index) v2.(vote_target_hash)
         v2.(vote_target_epoch) v2.(vote_source_epoch)
         v2.(vote_sig)
    /\ [&& vote_target_hash v1 == vote_target_hash v2,
           vote_target_epoch v1 == vote_target_epoch v2
           & vote_source_epoch v1 == vote_source_epoch v2] = false
    /\ [|| vote_target_epoch v1 == vote_target_epoch v2,
          (vote_target_epoch v2 < vote_target_epoch v1) &&
          (vote_source_epoch v1 < vote_source_epoch v2)
        | (vote_target_epoch v1 < vote_target_epoch v2) &&
          (vote_source_epoch v2 < vote_source_epoch v1)]) \/
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

  (* Destruct remaining conditions in if statement. *)
  destruct ([|| vote_target_epoch v1 == vote_target_epoch v2,
                (vote_target_epoch v2 < vote_target_epoch v1) &&
                (vote_source_epoch v1 < vote_source_epoch v2)
              | (vote_target_epoch v1 < vote_target_epoch v2) &&
                (vote_source_epoch v2 < vote_source_epoch v1)]) eqn:H5.

  (* all true case: st, sa updated *)
  - do 7 right; left. exists s; split; auto. exists v; split; auto.
    inversion H. move/eqP in H.
    by exists w; repeat split.

  (* not (target_hash, tearget_epoch, source_epoch for v1/v2 equal) *)
  - do 6 right; left. exists s; split; auto. exists v; split; auto. move/eqP in H3.
    inversion H; subst. exists w; repeat split; auto.
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
Qed.

(* TODO: Account for rewards *)
Lemma procContractCallTx_VoteCall :
  forall (s : Sender) (block_number : nat) (st st' : CasperData) (vote : Vote) (sa : seq SendAccount),
    procContractCallTx block_number (mkTx s (VoteCall vote)) st = (st', sa) ->
    (find vote.(vote_validator_index) st.(casper_validators) = None
      /\ st' = st /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ find vote.(vote_target_epoch) st.(casper_epochs) = None
      /\ st' = st /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ find vote.(vote_source_epoch) st.(casper_epochs) = None
      /\ st' = st /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ exists ted, find vote.(vote_target_epoch) st.(casper_epochs) = Some ted
      /\ exists sed, find vote.(vote_source_epoch) st.(casper_epochs) = Some sed
      /\ ~ sed.(epoch_is_justified)
      /\ st' = st /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ exists ted, find vote.(vote_target_epoch) st.(casper_epochs) = Some ted
      /\ exists sed, find vote.(vote_source_epoch) st.(casper_epochs) = Some sed
      /\ sed.(epoch_is_justified)
      /\ ~ vote.(vote_validator_index) \notin ted.(epoch_voted)
      /\ st' = st /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ exists ted, find vote.(vote_target_epoch) st.(casper_epochs) = Some ted
      /\ exists sed, find vote.(vote_source_epoch) st.(casper_epochs) = Some sed
      /\ sed.(epoch_is_justified)
      /\ vote.(vote_validator_index) \notin ted.(epoch_voted)
      /\ ~ sigValid_epochs validator.(validator_addr) vote.(vote_validator_index)
                           vote.(vote_target_hash) vote.(vote_target_epoch)
                           vote.(vote_source_epoch) vote.(vote_sig)
      /\ st' = st /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ exists ted, find vote.(vote_target_epoch) st.(casper_epochs) = Some ted
      /\ exists sed, find vote.(vote_source_epoch) st.(casper_epochs) = Some sed
      /\ sed.(epoch_is_justified)
      /\ vote.(vote_validator_index) \notin ted.(epoch_voted)
      /\ sigValid_epochs validator.(validator_addr) vote.(vote_validator_index)
                           vote.(vote_target_hash) vote.(vote_target_epoch)
                           vote.(vote_source_epoch) vote.(vote_sig)
      /\ find vote.(vote_source_epoch)
                    (casper_epochs
                       {[st with casper_epochs := upd (vote_target_epoch vote)
                         {[ted with epoch_voted := rcons (epoch_voted ted)
                                                         (vote_validator_index vote)]}
                         (casper_epochs st)]}) = None
      /\ st' = {[st
                 with casper_epochs := upd vote.(vote_target_epoch)
                                           {[ted
                                             with epoch_voted := rcons ted.(epoch_voted)
                                                                       vote.(vote_validator_index)]}
                                           st.(casper_epochs)]}
      /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ exists ted, find vote.(vote_target_epoch) st.(casper_epochs) = Some ted
      /\ exists sed, find vote.(vote_source_epoch) st.(casper_epochs) = Some sed
      /\ sed.(epoch_is_justified)
      /\ vote.(vote_validator_index) \notin ted.(epoch_voted)
      /\ sigValid_epochs validator.(validator_addr) vote.(vote_validator_index)
                           vote.(vote_target_hash) vote.(vote_target_epoch)
                           vote.(vote_source_epoch) vote.(vote_sig)
     /\ exists e1, find vote.(vote_source_epoch)
                             (casper_epochs
                                {[st with casper_epochs := upd (vote_target_epoch vote)
                                  {[ted with epoch_voted := rcons (epoch_voted ted)
                                                                  (vote_validator_index vote)]}
                                  (casper_epochs st)]}) = Some e1
      (* FIXME: ... == false is lazy *)
      /\ (vote_target_epoch vote == vote_source_epoch vote + 1) == false
      /\ st' = {[st
                 with casper_epochs := upd vote.(vote_target_epoch)
                                           {[ted
                                             with epoch_voted := rcons ted.(epoch_voted)
                                                                       vote.(vote_validator_index)]}
                                           st.(casper_epochs)]}
      /\ sa = [::]) \/
    (exists validator, find vote.(vote_validator_index) st.(casper_validators) = Some validator
      /\ exists ted, find vote.(vote_target_epoch) st.(casper_epochs) = Some ted
      /\ exists sed, find vote.(vote_source_epoch) st.(casper_epochs) = Some sed
      /\ sed.(epoch_is_justified)
      /\ vote.(vote_validator_index) \notin ted.(epoch_voted)
      /\ sigValid_epochs validator.(validator_addr) vote.(vote_validator_index)
                         vote.(vote_target_hash) vote.(vote_target_epoch)
                         vote.(vote_source_epoch) vote.(vote_sig)
      /\ exists e1, find vote.(vote_source_epoch)
                         (casper_epochs
                            {[st with casper_epochs := upd vote.(vote_target_epoch)
                              {[ted with epoch_voted := rcons ted.(epoch_voted)
                                                              vote.(vote_validator_index)]}
                              st.(casper_epochs)]}) = Some e1
      /\ st' = {[{[{[st
           with casper_epochs := upd vote.(vote_target_epoch)
             {[ted with epoch_voted := rcons ted.(epoch_voted)
                                             vote.(vote_validator_index)]}
             (casper_epochs st)]}
                   with casper_epochs := upd vote.(vote_target_epoch)
                     {[e1 with epoch_is_finalized := true]}
                     (casper_epochs
                       {[st with casper_epochs := upd vote.(vote_target_epoch)
                         {[ted with epoch_voted := rcons ted.(epoch_voted)
                                                         vote.(vote_validator_index)]}
                         st.(casper_epochs)]})]}
                with casper_last_finalized_epoch := vote.(vote_source_epoch)]}
      /\ sa = [::]).
Proof.
  intros. unfold procContractCallTx, tx_call, tx_sender, finalize, justify, reward in H.

  (* Case match on existence of validator. Trivially discharge goal if none. *)
  destruct (find (vote_validator_index vote) (casper_validators st));
    last by left; inversion H.

  (* Case match on existence of target epoch data. Trivially discharge goal if none. *)
  destruct (find (vote_target_epoch vote) (casper_epochs st));
    last by right; left; exists v; inversion H.

  (* Case match on existence of source epoch data. Trivially discharge goal if none. *)
  destruct (find (vote_source_epoch vote) (casper_epochs st));
    last by do 2 right; left; exists v; inversion H.

  (* Case match on boolean conditions of if statement in H. *)
  destruct (epoch_is_justified e0) eqn:H1.
  destruct (vote_validator_index vote \notin epoch_voted e) eqn:H2.
  destruct (sigValid_epochs (validator_addr v) (vote_validator_index vote)
                            (vote_target_hash vote) (vote_target_epoch vote)
                            (vote_source_epoch vote) (vote_sig vote)) eqn:H3.

  destruct (find (vote_source_epoch vote)
           (casper_epochs
              {[st
              with casper_epochs := upd (vote_target_epoch vote)
                                      {[e
                                      with epoch_voted := rcons (epoch_voted e)
                                                            (vote_validator_index vote)]}
                                      (casper_epochs st)]})) eqn:H4.

  destruct (vote_target_epoch vote == vote_source_epoch vote + 1) eqn:H5.

  (* All true case *)
  - repeat right.
    exists v; split; auto; exists e; split; auto; exists e0.
    inversion H; subst. repeat split; auto.
    by exists e1.

  (* False case: vote_target_epoch vote == vote_source_epoch vote + 1) = false *)
  - do 7 right; left.
    exists v; split; auto; exists e; split; auto; exists e0.
    inversion H; subst. repeat split; auto.
    by exists e1; repeat split; auto.

  (* False case: vote_target_epoch vote == vote_source_epoch vote + 1) = false *)
  - do 6 right; left.
    by inversion H; exists v; split; auto; exists e; split; auto; exists e0.

  (* False case: signature is not valid *)
  - do 5 right; left.
    inversion H; exists v; split; auto; exists e; split; auto; exists e0.
    by move/negP in H3.

  (* False case: validator has already voted *)
  - do 4 right; left.
    inversion H; exists v; split; auto; exists e; split; auto; exists e0; repeat split; auto.
    by move/negP in H2; move/negP.

  (* False case: source epoch not justified *)
  - do 3 right; left.
    inversion H; exists v; split; auto; exists e; split; auto; exists e0.
    by move/negP in H1.
Qed.
