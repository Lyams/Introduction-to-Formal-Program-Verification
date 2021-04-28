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

Print ex.
(*p14 or 17 sverhu*)

Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).
Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof. 
(* move=> x; case=> y Rxy. *) move=> x [y Rxy].
by apply: R_trans _ (R_sym _ y _).
Qed.

End R_sym_trans.

Section Smullyan_drinker.
Variables (D : Type)(P : D -> Prop).
Hypothesis (d : D) (EM : forall A, A\/~A).

Lemma drinker : exists x, P x -> forall y, P y.
Proof.
case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy];
  first by exists y.
exists d => _ y; case: (EM (P y)) => // notPy.
by case: nonotPy; exists y. Qed.

End Smullyan_drinker.

Section Equality.
Variables f : nat -> nat.
Hypothesis f00 : f 0 = 0.

Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
move=> k k0. by rewrite k0. Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k.
Proof. by move=> k ->. Qed.

Variable f10 : f 1 = f 0.

Lemma ff10 : f (f 1) = 0.
Proof. (* rewrite f10. rewrite f00. by [].*)
by rewrite f10 f00.
Qed.

Variables (D : eqType) (x y : D).
About eqP.

Lemma eq_prop_bool : x = y -> x == y.
Proof. by move/eqP. Qed.

Lemma eq_bool_prop : x == y -> x = y.
Proof. by move/eqP. Qed.

End Equality.

Section Using_Definition.
Variable U : Type.
Definition set := U -> Prop.
Definition subset (A B : set) := forall x, A x -> B x.
Definition transitive (T : Type) (R : T -> T -> Prop) :=
  forall x y z, R x y -> R y z -> R x z.
Check Prop.

Lemma subset_trans : transitive set subset.
Proof.
rewrite /transitive /subset => x y z subxy subyz t xt.
by apply: subyz; apply: subxy.
Qed.

Lemma subset_trans2 : transitive set subset.
Proof. move=> x y z subxy subyz t.
by move/subxy; move/subyz.
Qed.

End Using_Definition.

(* 19 pages - 22 vverhu*)

Lemma three : S (S (S O)) = 3 /\ 2 = 0.+1.+1.
Proof. by []. Qed.

Print plus.
Print Nat.add.

Lemma concrete_plus : plus 16 64 = 80.
Proof. by []. Qed.

Print addn.
Print muln.
Print Nat.mul.
Print le.

(* page 21 - vverhu 24 *)
About Le.le_n_Sn.
Lemma concrete_le : le 1 3.
Proof. by apply: (Le.le_trans _ 2); apply: Le.le_n_Sn.
(* apply: (Le.le_trans _ 2). apply: Le.le_n_Sn.
 apply: Le.le_n_Sn. *) Qed.

Lemma concrete_big_le : le 16 64.
Proof. by auto 47 with arith. Qed.

Print leq.

Lemma concrete_big_leq : 0 <= 51.
Proof. by []. Show Proof. Qed.

Lemma semi_concrete_leq : forall n m,
  n <= m -> 51 + n <= 51 + m.
Proof. by []. Qed.

Lemma concrete_arith : (50 < 100) &&
  (3 + 4 < 3 * 4 <= 17 - 2).
Proof. by []. Qed.

Check nat_ind.

Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
elim=> [m1 | n1 IHn1 m1].
  elim: m1 => // m1 IHm1. 
rewrite -[0 + m1.+1]/(0 + m1).+1 IHm1. by [].
rewrite -[n1.+1 + m1]/(n1 + m1).+1 IHn1.
elim: m1 => // m1 IHm1.
rewrite -[m1.+1 + n1]/(m1 + n1).+1 IHm1.
by [].
Qed.

(* 25 page - vverhu 28 *)

















