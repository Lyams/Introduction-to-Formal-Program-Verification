(* https://hal.inria.fr/inria-00407778/document *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.

Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) ->
  (A -> B) -> A -> C.
Proof.
move => hABC hAB hA.
move: hABC.
apply.
by [].
move: hAB.
apply.
done.
Qed.