From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Usage :

rewrite (ACl operator reordering)

- operator must be a (canonical) Monoid.com_law
- reordering is expressed using the syntax
  s := n | s + s' (where "+" is purely formal)
  where n is a nat
- we assume the lhs is associated to the left
  (use !opA before ACl if required)

Examples of syntax :
- (0 + 1) + 2 is the identity
- (0 + 2) + 1 correspond to opAC
- 0 + (1 + 2) is the same as chaining -opA and opCA
...
*)

Delimit Scope AC_scope with ac.

Section AC.

Inductive syntax := Leaf of nat | Op of syntax & syntax.
Definition seqtax :=
  (fix aux (acc : seq nat) (s : syntax) := match s with
               | Leaf n => n :: acc
               | Op s s' => (aux^~ s (aux^~ s' acc))
               end) [::].

Definition sfoldl R (d : R) f (s : seq R) :=
  if s is a::s then foldl f a s else d.
Definition sfoldr R (d : R) f (s : seq R) :=
  if s is a::s then foldr f a s else d.

Variables (T : Type) (default : T) (env : seq T) (op : Monoid.com_law default).

Local Notation "x + y" := (op x y).

Definition desyntax :=
  fix aux (s : syntax)  := match s with
               | Leaf n => nth default env n
               | Op s s' => aux s + aux s'
               end.

Lemma ACl_def s :
  let st := seqtax s in let sst := size st in let isst := iota 0 sst in
                                              perm_eq st isst ->
  sfoldl default op (map (nth default env) isst) = desyntax s.
Proof.
have seqtax_Op s1 s2 : seqtax (Op s1 s2) = seqtax s1 ++ seqtax s2.
  rewrite /seqtax; set aux := (X in X [::]); rewrite -/aux.
  elim: s1 (aux [::] s2) => [n|s11 IHs1 s12 IHs2] //= l.
  by rewrite IHs1 [in RHS]IHs1 IHs2 catA.
move=> st sst isst pst.
transitivity (\big[op/default]_(i <- isst) nth default env i).
  case: isst {pst} => [|x l /=]; rewrite (big_nil, big_cons) //=.
  elim: l (nth _ _ _) => [|y l IHl] x0.
    by rewrite big_nil ?Monoid.mulm1.
  by rewrite big_cons /= IHl Monoid.mulmA.
elim: s => [n|s IHs s' IHs'] //= in st sst (isst) pst *.
  have [/perm_eq_size {pst}] := (pst, pst).
  case: isst => // m [|//] _ /perm_eqP/(_ (pred1 m)) => /=.
  by rewrite eqxx; case: eqP => //= ->; rewrite big_cons big_nil Monoid.mulm1.
have /(eq_big_perm _) <- := pst.
by rewrite [st]seqtax_Op big_cat IHs ?IHs' //.
Qed.

End AC.

Coercion Leaf : nat >-> syntax.
Bind Scope AC_scope with syntax.
Notation "0" := 0%N : AC_scope.
Notation "1" := 1%N : AC_scope.
Notation "x * y" := (Op x%ac y%ac) : AC_scope.

Definition type_of T (x : T) := T.
Arguments type_of / T x.
Definition lhs T a b (e : a = b :> T) := a.
Arguments lhs / T a b e.
Definition rhs T a b (e : a = b :> T) := b.
Arguments rhs / T a b e.

Import Classes.Init.
Class envn T (n : nat) := Envn : seq T.
Instance envn0 T : envn T 0 := nil.
Definition consn T n x {s : envn T n} : envn T n.+1 := x :: s.
Hint Extern 0 (envn _ (S _)) =>
  match goal with |- envn ?T (S ?n) =>
                  let x := fresh "x" in
                  evar (x : T); apply (@consn _ _ x _)
  end : typeclass_instances.

Class compute T x y := Compute : x = y :> T.
Hint Extern 0 (@compute _ _ _) => compute; reflexivity : typeclass_instances.
Class simpl T x y := Simpl : x = y :> T.
Hint Extern 0 (@simpl _ _ _) => simpl; reflexivity : typeclass_instances.

Definition ACl_auto T default (law : Monoid.com_law default) (s : syntax)
   {peq : compute (perm_eq (seqtax s) (iota 0 (size (seqtax s)))) true}
   {sst} {_ : compute (size (seqtax s)) sst}
   {env : envn T sst}
   (use := @ACl_def T default env law s peq)
   {lhs'} {elhs : simpl (lhs use) lhs'}
   {rhs'} {erhs : simpl (rhs use) rhs'}
   : lhs' = rhs' :=
  (match elhs with erefl =>
    (match erhs with erefl => use end) end).

Notation ACl_of f s := (@ACl_auto _ _ [com_law of f] s%ac
                                isT _ _ _ _ _ _ _).
Notation ACl f s := (ACl_of f s%ac : f%function _ _ = _).

Section Tests.

Lemma test_orb (a b c d : bool) : (a || b) || (c || d) = (a || c) || (b || d).
Proof.
rewrite !orbA.
rewrite (ACl orb ((0 * 2) * (1 * 3))).
by rewrite !orbA.
Qed.

Lemma test_addn (a b c d : nat) : (a + b + c + d = a + c + b + d)%N.
Proof.
by rewrite (ACl addn (0 * 2 * 1 * 3)).
Qed.

End Tests.
