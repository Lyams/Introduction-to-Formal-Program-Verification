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

End My.