From mathcomp
Require Import all_ssreflect.

Section StrongInduction.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0.

  Lemma pred_increasing : forall (n m : nat),
      n <= m ->
      n.-1 <= m.-1.
  Proof. by elim => //= n IH'; case. Qed.

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    elim => //=; first by case.
    move => n IH' m Hm.
    apply: IH.
    move => n' Hn'.
    apply: IH'.
    have Hnn: n < n.+1 by apply ltnSn.
    move: Hm.
    rewrite leq_eqVlt.
    move/orP.
    case.
    - move/eqP => Hm.
      by move: Hm Hn' =>->.
    - move => Hm.
      have Hmn: m <= n by [].
      suff Hsuff: n' < n.
        rewrite leq_eqVlt.
        apply/orP.
        by right.
      by apply: leq_trans; eauto.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.
