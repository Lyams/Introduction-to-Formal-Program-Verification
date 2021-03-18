From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Module MyNamespace.

Definition idb := fun b : bool => b.

Fail Definition id : A -> A := fun x : A => x.

Definition id :
  forall A : Type, A -> A
:= fun A : Type => fun x : A => x.

Compute id bool true.
Compute id nat 42.

Check id bool : bool -> bool.
Check id nat : nat -> nat.

Locate "->".

Definition id' :
  forall A : Type, forall x : A, A
:= fun A : Type => fun x : A => x.

Inductive prodn : Type := | pairn of nat & nat.
Print prodn.

Inductive prod (A B : Type) : Type :=
  | pair of A & B.

Fail Check prod : Type.
Check prod nat nat : Type.
Check pair.

Check pair nat bool 42 true : prod nat bool.

Arguments id [A] _.
Arguments pair [A B] _ _.

Check id 42.
Compute id 42.
Check pair 42 true.
Compute pair 42 true.
Fail Check pair nat bool 42 true : prod nat bool.
Check @pair nat bool 42 true : prod nat bool.
Check @pair _ _ 42 true : prod _ _.

Set Printing Implicit.
Check pair 42 true : prod nat bool.
Unset Printing Implicit.

Set Implicit Arguments.

Notation "A * B" :=
  (prod A B)
  (at level 40, left associativity)
  : type_scope.

Locate "*".

Fail Check nat * bool.
Check (nat * nat)%type.
Check (nat * bool) : Type.
Open Scope type_scope.
Locate "*".
Check (nat * nat).
Check (( nat * bool) * nat)%type.
Check (nat * bool * nat)%type.
Check ( nat * (bool * nat))%type.

Notation "( p , q , .. , r )" :=
  (pair .. (pair p q) .. r) : core_scope.

Check (1, false) : nat * bool.
Check (1, false, 3) : nat * bool * nat.
Check (1, false, 3, true) : nat * bool * nat * bool.

Definition fst {A B : Type} : A * B -> A :=
  fun p =>
    match p with
    | (a, _) => a
    end.

Unset Printing Notations.
Print fst.
Set Printing Notation.

Definition snd {A B : Type} : A * B -> B :=
  fun p =>
    match p with
    | pair _ b => b
    end.

Notation "p .1" := (fst p).
Notation "p .2" := (snd p).

Compute (42, true).1.
Compute (42, true).2.
Definition sap {A B : Type} : A * B -> B * A :=
  fun p =>
    match p with
    | (a,b) => (b,a)
    end.
