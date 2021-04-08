From mathcomp Require Import ssreflect
ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma A_imp_A :
  forall (A : Prop), A -> A.
Proof.
  move => A.
  move => proof_A.
  exact: proof_A.
  Qed.
About A_imp_A.

Lemma A_imp_A' :
  forall (A : Prop), A -> A.
Proof.
  intros A.
  move => proof_A.
  exact: proof_A.
  Qed.

Lemma A_implies_A' :
  forall (A : Prop), A -> A.
Proof.
move=> A.
Show Proof.
move=> proof_A.
Show Proof.
exact: proof_A.
Show Proof.
Unset Printing Notations.
Show Proof.
Set Printing Notations.
Qed.

Lemma A_imp_B_imp_A (A B : Prop) :
  A -> B -> A.
Proof.
move => a.
move => _.
exact: a.
Qed.

Lemma modus_ponens (A B : Prop) :
  A -> (A -> B) -> B.
Proof.
move=> a.
apply.
exact: a.
Qed.

Definition and1 (A B : Prop) :
  A /\ B -> A.
Proof.
case.
move=> a _.
exact: a.
Qed.

Definition andC (A B : Prop) :
  A /\ B -> B /\ A.
Proof.
case.
move => a b.
split.
exact: b.
exact: a.
Qed.

Definition orC (A B : Prop) :
  A \/ B -> B \/ A.
Proof.
case.
move => a.
  right.
  exact: a.
move => b.
left.
exact: b.
Qed.

Lemma or_and_distr A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case.
- move => a c.
  left.
  split.
  - exact: a.
  exact: c.
move => b c.
right.
split.
- exact: b.
exact: c.
Qed.

Lemma or_and_distr1 A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case => [a|b] c.
- by left.
by right.
Qed.

Lemma or_and_distr2 A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof. by case=> [[a|b] c]; [left | right]. Qed.

Lemma HilberSaxiom A B C :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  move => abc ab a.
  move: abc.
  apply.
  - by [].
  move: ab.
  apply.
  done. (* exact: a. *)
Qed.

Lemma HilberSaxiom1 A B C :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof. 
  move => abc ab a.
  apply: abc.
  - by [].
  by apply: ab. (* apply: ab. exact: a.*)
  Qed.

Lemma HilberSaxiom2 A B C :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  move => abc ab a.
  apply: abc => //.
  by apply: ab.
  Qed.

Section RewriteTactic.

Variable A : Type.
Implicit Types x y z : A.

Lemma esym x y :
  x = y -> y = x.
Proof.
  move => x_eq_y.
  rewrite x_eq_y.
  by []. (* done. *)
Qed.

Lemma eq_sym_shorter x y :
  x = y -> y = x.
Proof.
  move => ->.
  done.
Qed.

Lemma eq_trans x y z :
  x = y -> y = z -> x = z.
Proof.
  move=> ->.
  done.
Qed.

End RewriteTactic.

Lemma addnA :
  associative addn.
Proof.
  rewrite / associative.
  move => x y z.
Restart.
  Show.
  move=> x y z.
  move: x.
  elim.
  Show Proof.
  Check nat_ind.
  -   by [].
  move=> x IHx.
  Fail rewrite IHx.
  Search (_.+1 + _).
  rewrite addSn.
  rewrite IHx.
  done.
Restart.
  by move=> x y z; elim: x=> // x IHx; rewrite addSn IHx.
Qed.