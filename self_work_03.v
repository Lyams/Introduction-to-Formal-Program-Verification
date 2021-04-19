(* https://hal.inria.fr/inria-00407778/document *)
From mathcomp Require Import ssreflect
ssrbool eqtype ssrnat.

Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) ->
  (A -> B) -> A -> C.
Proof.
move => hABC hAB hA.
(*generalize hABC.  does not clear the
hypothesis from the context*)
revert hABC. (*move: hABC. *)
apply. by [].
(* move: hAB; apply. done. *)
(* move: hAB. apply. done. *)
by apply: hAB. Qed.

Hypotheses (hAiBiC : A -> B -> C)
  (hAiB : A -> B) (hA : A).
Lemma HilbertS2: C.
Proof.
apply: hAiBiC; first by apply: hA.
exact: hAiB. Qed.

Lemma HilbertS3 : C.
Proof. by apply: hAiBiC; last exact: hAiB. Qed.

Lemma HilbertS4 : C.
Proof. exact: (hAiBiC _ (hAiB _)). Qed.

Lemma HilbertS5 : C.
Proof. exact: hAiBiC (hAiB _). Qed.

Lemma HilbertS6: C.
Proof. exact: HilbertS5. Qed.

Print HilbertS5.
Print HilbertS2.
Check HilbertS.

End HilbertSaxiom.

Print HilbertS5.
Print HilbertS.


Print bool.

(* page 11 (14 vverhu) *)
Section Symmetric_Conjunction_Disjunction.


End Symmetric_Conjunction_Disjunction.

