From mathcomp Require Import ssreflect
ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma addnC :
  commutative addn.
Proof.
move=> x y.
elim: x.
- rewrite add0n.
  elim: y=> // y IHy.
  rewrite addSn -IHy.
  done.
Restart.
elim=> [| x IHx] y; first by rewrite addn0.
by rewrite addSn IHx -addSnnS.
Qed.

Locate "`!".
Print factorial.
Print fact_rec.

Fixpoint factorial_helper (n : nat) (acc : nat) : nat :=
  if n is n'.+1 then
    factorial_helper n' (n * acc)
  else
    acc.

Definition factorial_iter (n : nat) : nat :=
  factorial_helper n 1.

Lemma factorial_iter_correct n :
  factorial_iter n = n`!.
Proof. elim: n. - done. move=> n IHn.
rewrite /factorial_iter.
move=> /=. rewrite muln1.
rewrite /factorial_iter in IHn.
Abort.

Lemma factorial_helper_correct n acc :
  factorial_helper n acc = n`! * acc.
Proof.
elim: n=> [|n IHn /=]; first by rewrite fact0 mul1n.
Restart.
move: acc.
elim: n.
- move=> acc.
  by rewrite fact0 mul1n.
move=> n IHn acc /=.
rewrite IHn.
by rewrite factS mulnCA mulnA.
Restart.
elim: n acc=> [|n IHn /=] acc; first by rewrite fact0 mul1n.
by rewrite IHn factS mulnCA mulnA.
Qed.

Lemma factorial_iter_correct n :
  factorial_iter n = n`!.
Proof.
rewrite /factorial_iter.
by rewrite factorial_helper_correct muln1.
Qed.

Search (1 * _).
Search _ left_id.
