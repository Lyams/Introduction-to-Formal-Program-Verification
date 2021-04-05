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
End My.