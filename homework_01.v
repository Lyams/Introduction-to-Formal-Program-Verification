From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Local Open Scope nat_scope.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb (b c : bool) : bool := 
  match b with
  | false => c
  | true => true
  end.
Check orb.
Compute orb true false.
Compute orb false true.
Compute orb false false.
Compute orb true true.


(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool :=
    match b with
    | false => c
    | true => negb(c)
    end.
Check addb.
Compute addb true false.
Compute addb false false.
Compute addb true true.
Compute addb false true.
(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool := 
    match b with
    | true => c
    | false => negb(c)
    end.
Check eqb.
Compute eqb true true.
Compute eqb false false.
Compute eqb true false.
Compute eqb false true.

(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat := 
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.
Check dec2.
Compute dec2 (S(S (S (S (S (S (S O))))))).
Compute dec2 (S O).
Compute dec2 O.
Compute dec2 (S( S O)).


(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) {struct n} : nat :=
    if m is (S m') then
    match n with
    | O => m
    | (S n') => subn m' n'
    end
    else O.
Check subn.
Compute subn (S O) (S O).
Compute subn (S(S(S O))) (S O).
Compute subn (S(S(S(S O)))) (S(S(S O))).
Compute subn O (S O).
Compute subn (S(S(S(S O)))) (S O).
(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint addn (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S n' => S (addn n' m)
    end.
Compute addn (S(S(S(O)))) (S(S(S(S(O))))).

Fixpoint muln (m n : nat) {struct m}  : nat :=
    match m with
    | O => O
    | S p => addn n (p * n)
    end
where "p * n" := (muln p n ) : nat_scope.
(**     if m is (S m') then addn n (mult m' n)
     else O. *)
Check muln.
Compute muln O O.
Compute muln (S(S(S(S(S O))))) (S(S(O))).
Compute muln (S O) O.
Compute muln O (S O).
Compute muln (S O) (S O).
Compute muln (S O) (S(S(S O))).

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool := 
    if m is (S m') then if n is (S n')
                          then eqn m' n'
                          else false
      else if n is O then true else false.
Check eqn.
Compute eqn O O.
Compute eqn (S O) (S O).
Compute eqn (S(S(S O))) (S(S(S O))).
Compute eqn O (S(S(S O))).
Compute eqn (S(S(S O)))(S(S O)).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Fixpoint leq (m n : nat) : bool := 
    if m is (S m') then if n is (S n')
                          then leq m' n'
                          else false
     else true.
Check leq.
Compute leq O O.
Compute leq (S O) (S O).
Compute leq (S(S(S O))) (S(S(S O))).
Compute leq O (S(S(S O))).
Compute leq (S(S(S O)))(S(S O)).


(*| ---------------------------------------------------------------------------- |*)
Definition lt (a b : nat) : bool := negb (eqn (subn b a) O).


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)
Fixpoint subn'' (a b : nat) : nat :=
  if a is S a' then (if b is S b' then subn'' a' b' else a) else a.

Fixpoint subn' ( a b : nat) : nat :=
  match a with 
  | S a' => if b is S b' then subn' a' b' else a
  | O => a
  end.
Fixpoint divn (m n : nat) {struct m} : nat :=
  if n is S n' then    if subn'' m n' is S m' then S (divn m' n) else O  else O.
Check eq_refl : divn (S(S(S(S(O))))) (S(S O)) = S(S O).
 
End My.
