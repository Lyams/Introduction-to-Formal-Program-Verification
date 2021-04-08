From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
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
move=> a.
  right.
  exact: a.
move=> b.
left.
exact: b.
Qed.

Lemma or_and_distr A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case.
- move=> a c.
  left.
  split.
  - exact: a.
  exact: c.
move=> b c.
right.
split.
- exact: b.
exact: c.
Qed.


