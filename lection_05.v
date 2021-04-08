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