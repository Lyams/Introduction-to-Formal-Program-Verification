From mathcomp Require Import ssreflect.

(* implement functions with the given signatures *)
Check prod.

Definition prodA (A B C : Type) :
  (A * B) * C -> A * (B * C)
:= 
  fun '(a, b, c) => (a,(b,c)).
Check prodA.
Print sum.

Definition sumA (A B C : Type) :
  (A + B) + C -> A + (B + C)
:= fun s =>
  match s with
  | inl ab => match ab with
                | inl a => inl a
                | inr b => inr (inl b) end
  | inr c => inr (inr c) end.
Print sumA.
Definition sumA_ (A B C : Type) :
  (A + B) + C -> A + (B + C)
:= fun s  => match s with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition prod_sumD (A B C : Type) :
  A * (B + C) -> (A * B) + (A * C)
:= fun d => match d with
  | (a, (inl b)) => inl (a, b)
  | (a, (inr c)) => inr (a,c)
  end.

Definition sum_prodD (A B C : Type) :
  A + (B * C) -> (A + B) * (A + C)
:= fun pd => match pd with
  | inl a => (inl a, inl a)
  | inr (b, c) => (inr b, inr c)
  end.


(* function composition *)
Definition comp A B C (f : B -> A) (g : C -> B) : C -> A
:= fun x => f (g x).

Notation "f \o g" := (comp _ _ _ f g)
  (at level 90, right associativity).

Compute (( S \o S) (S(O))).
Check eq_refl : (( S \o S) (S(O))) = 3.
(* Introduce a notation that lets us use composition like so: f \o g.
   You might need to tweak the implicit status of some comp's arguments *)


(* Introduce empty type, call `void` *)
Inductive void : Type := .
Definition void_terminal (A : Type) :
  void -> A
:= fun x => match x with end.

Variable x : void.
Check (void_terminal _ x).
Check match x with end : nat.
Check match x with end : (nat * nat).
Check match x with end : void.
Check match x with end : bool.

Compute (void_terminal nat x : nat).

(* Introduce `unit` type (a type with exactly one canonical form) *)
Inductive unit := tt.
Definition unit_initial (A : Type) :
  A -> unit
:= fun _ => tt.


(* Think of some more type signatures involving void, unit, sum, prod *)