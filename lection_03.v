From mathcomp Require Import ssreflect ssrfun.
Set Implicit Arguments.

Module My.

Definition A_implies_A (A : Prop) :
  A -> A
:= fun proof_of_A : A => proof_of_A.

Definition A_implies_B_implies_A (A B : Prop) :
  A -> B -> A
:= fun proof_A => fun proof_B => proof_A.

Definition modus_ponens (A B : Prop) :
  A -> (A -> B) -> B
:= fun pA pAimpliesB => pAimpliesB pA.

Inductive and (A B : Prop) : Prop :=
  | conj of A & B.

Notation "A /\ B" := (and A B) : type_scope.

Inductive prod (A B : Type) : Type :=
  | pair of A&B.

Definition andC (A B : Prop) :
  A /\ B -> B /\ A :=
  fun pAandB =>
  match pAandB with
  | conj pA pB => conj pB pA
  end.

Inductive or (A B : Prop) : Prop :=
  | or_introl of A
  | or_intror of B.

Notation "A \/ B" := (or A B) : type_scope.

Arguments or_introl [A] B _, [A B] _.
Arguments or_intror A [B] _, [A B] _.

Inductive sum (A B : Type) : Type :=
  | inl of A
  | inr of B.

Definition and_or_distr (A B C : Prop) :
  (A \/ B) /\ C -> (A /\ C) \/ (B /\ C)
:= fun '(conj paob pc) =>
  match paob with
     | or_introl pa => or_introl (conj pa pc)
     | or_intror pb => or_intror (conj pb pc)
     end.


Inductive True : Prop :=
  | I.

Definition anything_implies_True (A : Prop) :
  A -> True
:= fun _ => I.

Definition True_and_True :
  True /\ True
:= conj I I.

Inductive False : Prop := .

Definition exfalso_quodlibet {A : Prop} :
  False -> A
:= fun pF : False => match pF with end.

Definition a_or_false_implies_a (A : Prop) :
    A \/ False -> A
:= fun paof =>
    match paof with
    | or_introl pa => pa
    | or_intror pf => exfalso_quodlibet pf
    end.

Definition not (A : Prop) := A -> False.
Notation "~ A" := (not A) : type_scope.

Definition double_negation_introduction (A : Prop) :
  A -> ~ ~ A
:= fun pa : A => fun pna : ~ A => pna pa.


Definition iff (A B : Prop) := (A -> B) /\ (B -> A).
Notation "A <-> B" := (iff A B) : type_scope.

Definition forall_andD (A : Type) (P Q : A -> Prop) :
  (forall x, P x /\ Q x) ->
  (forall x, P x) /\ (forall x, Q x)
:= fun all_pq =>
     conj
       (fun x => match all_pq x with conj px _ => px end)
       (fun x => match all_pq x with conj _ qx => qx end).

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
  | ex_intro (x : A) (proof : P x).

Notation "’exists’ x : A , P" :=
  (ex (fun x : A => P))
    (at level 200, right associativity).

Notation "'exists' x .. y , p" :=
  (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition exists_not_forall A (P : A -> Prop) :
  (exists x, P x) -> ~ (forall x, ~ P x)
:=
  fun x_px : exists x, P x =>
    fun all_npx : forall x, ~ P x =>
      match x_px with
      | ex_intro x px => all_npx x px
      end.


Definition curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q)
:=
  fun f : (exists x, P x) -> Q =>
    fun x : A =>
      fun px : P x =>
        f (ex_intro P x px).

Inductive eq (A : Type) (x : A) : A -> Prop :=
  | eq_refl : eq x x.

Notation "x = y" := (eq x y) : type_scope.

Arguments eq_refl {A x}, {A} x.

Check eq_refl 0 : 0 = 0.
Check eq_refl : 0 = 0.
Check eq_refl : (fun _ => 0) 42 = 0.
Check eq_refl : 2 + 2 = 4.

Fail Check eq_refl : 0 = 1.
Variables A B : Type.
Variable f : A -> B.

Check eq_refl : f = f.


Check eq_refl : (fun x => x) = (fun y => y).

Check eq_refl : (fun x => f x) = f.

Definition eq_reflexive A (x : A) :
  x = x
:=
  eq_refl x.

Definition eq_sym_unannotated A (x y : A) :
  x = y -> y = x
:= fun (pf : x = y) =>
   (match pf with
    | eq_refl => (eq_refl x : x = x)
    end) : y = x. 

Definition eq_sym A (x y : A) :
  x = y -> y = x
:= fun (pf  : x = y) =>
     match
       pf in (_ = b)
       return (b = x)
     with
     | eq_refl => eq_refl x
     end.

About eq_sym.
Check eq_refl 42.
Check eq_sym (eq_refl (40 + 2)).

Definition eq_trans A (x y z : A) :
  x = y -> y = z -> x = z
:=
  fun pf_xy : x = y =>
    match
      pf_xy in (_ = b)
      return (b = z -> x = z)
    with
    | eq_refl => fun (pf_xz : x = z) => pf_xz
    end.

End My.