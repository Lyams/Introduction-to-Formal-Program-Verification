(* Logical Foundations
https://softwarefoundations.cis.upenn.edu/current/index.html *)

Module My.
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday ( d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_weekday sunday).

Compute (next_weekday (next_weekday friday)).

Example test_n_w: (next_weekday (next_weekday sunday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type := true | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  |false => true
  end.

Definition andb (a : bool) (b : bool) : bool :=
  match a with
  | true => b
  | false => false
  end.
Notation "x && y" := (andb x y).
Example test_andb1: (andb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (true && true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb3: (andb true (andb false true)) = false.
Proof. simpl. reflexivity. Qed.

Definition orb (a : bool) (b : bool) : bool
:= match a with
  | true => true
  | false => b
  end.
Notation "x || y" := (orb x y).
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (nandb) *)
Definition nandb (a:bool) (b:bool) : bool
:= match a, b with
  | true, true => false
  | true, false => true
  | false, _ => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (andb3) *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
:=  match b1 with
  | true => b2 && b3
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check negb : bool -> bool.
Fail Check negb : bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.

Inductive bit : Type := B0 | B1.
Inductive nybble : Type := bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B0 B0) : nybble.

Definition all_zero (nb : nybble) : bool
:= match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.
Check (S (S (S (S O)))).
Definition minustwo (n : nat) : nat
:= match n with
   | O => O
   | S O => O
   | S (S n') => n'
   end.

Compute (minustwo 10).
Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint evenb (n : nat) : bool
:= match n with
  | O => true
  | S O => false
  | S ( S n') => evenb n'
  end.

Definition oddb (x : nat) : bool := negb (evenb x).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.
Example test_evenb1: evenb 1 = false.
Proof. simpl. reflexivity. Qed.
Example test_evenb2: evenb 4 = true.
Proof. simpl. reflexivity. Qed.

Fixpoint exp (base power : nat) : nat
:= match power with
   | O => S O
   | S p => mult base (exp base p)
   end.

(*Exercise: 1 star, standard (factorial)*)
Fixpoint factorial (n:nat) : nat
:= match n with
  | O => 1
  | (S n') => n * (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
Compute (factorial 5).

Fixpoint eqb (n m : nat) : bool
:= match n with
   | O => match m with
         | O => true
         | S m' => false
         end
   | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
   end.
Fixpoint leb (n m : nat) : bool
:= match n with
   | O => true
   | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
   end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (ltb) *)
Definition ltb (n m : nat) : bool
:= leb (S n) m.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_ex : forall n m : nat,
  n = m -> n + n = m + m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

(* Exercise: 1 star, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m l : nat,
  n = m -> m = l -> n + m = m + l.
Proof. intros n m l. intros H. intros H1. rewrite -> H.
  rewrite -> H1. reflexivity. Qed.
Check plus_id_exercise.

Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof. Admitted.
Check mult_n_O.
Check mult_n_Sm.

(* Exercise: 1 star, standard (mult_n_1) *)
Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof. intros p. simpl. rewrite <- mult_n_Sm.
  rewrite <- mult_n_O. reflexivity. Qed.


End My.