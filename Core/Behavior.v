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
Admitted.

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


    
    
