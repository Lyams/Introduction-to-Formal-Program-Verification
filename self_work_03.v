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

Lemma andb_sym : forall A B : bool, A && B -> B && A.
Proof. case. by case. by []. Qed.

Lemma andb_sym2 : forall A B : bool, A && B -> B && A.
Proof. by case; case. Qed.

Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
Proof. by do 2! case. Qed.


Variables (C D : Prop) (hC : C) (hD : D).
Check (and C D).
Check (conj hC hD).

Lemma and_sym : forall A B : Prop, A /\B -> B/\A.
Proof. by move=> A1 B []. Qed.

Print or.

Lemma or_sym : forall A B : Prop, A\/B -> B\/A.
Proof. by move=> A B [hA | hB];
  [apply: or_intror | apply: or_introl]. Qed.

Lemma or_sym2 : forall A B : bool, A\/B -> B\/A.
Proof. 
(*case; case; move => AorB; apply/orP.
by move: AorB; move/orP.
by move: AorB; move/orP.
by move: AorB; move/orP.
by move: AorB; move/orP. *)

by move=> [] [] AorB; apply/orP;
   move/orP : AorB. Qed.
Print orP.

End Symmetric_Conjunction_Disjunction.

(p14 or 17 sverhu)