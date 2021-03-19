(* Logical Foundations
https://softwarefoundations.cis.upenn.edu/current/index.html *)

Module My.
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | satuday
  | sunday.

Definition next_weekday ( d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => satuday
  | satuday => sunday
  | sunday => monday
  end.


End My.