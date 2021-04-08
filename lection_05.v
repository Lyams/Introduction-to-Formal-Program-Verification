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