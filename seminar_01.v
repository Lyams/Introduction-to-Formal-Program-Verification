From mathcomp Require Import ssreflect.

Module My.

Inductive bool : Type :=
| true
| false.

Check false : bool.
Check false.
Check (bool -> bool) : Type.
Check (fun b : bool => b).
Check fun b => b.
Check (fun b =>b) true.
Check fun (f : bool -> bool) => f true.

Definition idb := fun b : bool => b.

Check idb.
Check (fun (f : bool -> bool) => f true) idb.
Compute idb false.
Fail Check (fun (f: bool -> bool) => f true) false.
Definition negb :=
 fun (b: bool) =>
    match b with
    | true => false
    | false => true
    end.
Check negb.
Compute negb false.
Compute negb true.

Eval cbv delta in negb true.
Eval cbv beta delta in negb true.
Eval cbv beta delta iota in negb true.
Variable c : bool.
Compute idb c.
Compute negb c.
Definition anbc (b c : bool) : bool :=
  match c with
  | false => false
  | true => b
  end.


Inductive nat : Type :=
  | O
  | S of nat.
Print nat.
Check O.
Check S O.
Check S (S O).
Check S (S (S O)).

Definition succn := S.
Compute succn (S (S O)).

Definition predn (n : nat) : nat :=
  match n with
  | S x => x
  | O => O 
  end.

Compute predn (S (S O)).
Compute predn  O.


Fixpoint addn (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => S (addn n' m)
  end.

Compute addn (S (S O)) (S (S O)).

Fixpoint addn_idiomatic (n m : nat) : nat :=
  if n is S n' then S (addn_idiomatic n' m) else m.
Compute addn_idiomatic (S (S O)) (S (S O)).

Definition add_no_sugar :=
  fix addn (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S n' => S (addn n' m)
    end.
Compute add_no_sugar (S (S O)) O.


End My.
Check My.nat.
Check My.addn.

From mathcomp Require Import ssrbool ssrnat.
Print addb.

About nat.
About S.

Check 42.

Check S(S O).