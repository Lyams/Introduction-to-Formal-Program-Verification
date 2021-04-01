From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition succ_inj (n m : nat) :
 n.+1 = m.+1 -> n = m
:= fun Sn_Sm : n.+1 = m.+1 =>
    match Sn_Sm in (_ = Sm) return ( n = Sm.-1)
    with
    | erefl => erefl n
    end.

Definition succ_inj' (n m : nat) :
  n.+1 = m.+1 -> n = m
:=  fun Sn_Sm => match Sn_Sm in _ = S q
                    return n = q with
                 | erefl => erefl n
                  end.

Definition or_inrol_inj (A B : Prop) (p1 p2 :A) :
  or_introl p1 = or_introl p2 :> (A \/ B) -> p1 = p2
:= fun eq =>
    match
      eq in (_ = oil2)
      return (p1 = if oil2 is or_introl p2'
                    then p2' else p2)
    with
    | erefl => erefl p1
    end.
About or_inrol_inj.
Print or_inrol_inj.

Definition false_eq_true_implies_false :
  false = true -> False
:= fun eq : false = true =>
    match eq in (_ = b)
              return (if b then False else True)
    with | erefl => I  end.

Definition false_eq_true_implies_false' :
  true = false -> False
:= fun eq :  true = false =>
    match eq in (_ = b)
              return (if b then True else False)
    with | erefl => I  end.
Print false_eq_true_implies_false.
Print False.
Print True.



Fail Definition or_introl_inj (A B : Prop) (p1 : A) (p2 : B) :
  or_introl p1 = or_intror p2 -> False
:=
  fun eq =>
    match
      eq in (_ = oil2)
      return (if oil2 is or_intror p2' then False else True)
    with
    | erefl => I
    end.

Locate "<>".
Definition neq_irrefl A (x : A) :
  x <> x -> False
:= fun neq_xx : x = x -> False =>
    neq_xx erefl.

Definition neq_sym A (x y : A) :
  x <> y -> y <> x
:= fun neq_xy : x <> y =>
    fun eq_yx : y = x =>
      (match
         eq_yx in (_ = a)
         return (a <> y -> False)
       with
       | erefl => fun neq_yy : y <> y => neq_yy erefl
       end) neq_xy.

Definition congr1 (A B : Type) :
  forall (f : A -> B) (x y : A),
    x = y -> f x = f y
:=
  fun f x y xy =>
    match
      xy in (_ = b)
         return (f x = f b)
    with
    | erefl => erefl (f x)
    end.


Fail Definition addn0 :
  forall n : nat, n + 0 = n
:=
  fun (n : nat) =>
    match n as a return (a + 0 = a) with
    | O => erefl 0
    | S n' => congr1 S (_ : n' + 0 = n')
    end.

Definition addn0 :
  forall n : nat, n + 0 = n
:= fix rec (n : nat) : n + 0 = n :=
    match n return (n + 0 = n) with
    | O => erefl 0
    | S n' => congr1 S (rec n')
    end.

Definition add0n :
  forall n : nat, 0 + n = n
:= fun n : nat => erefl n.

Definition nat_ind :
  forall (P : nat -> Prop),
          P 0 ->
          (forall n : nat, P n -> P n.+1) ->
          forall n : nat, P n
:= fun P =>
   fun (p0 : P 0) =>
   fun (step : (forall n : nat, P n -> P n.+1)) =>
      fix rec (n: nat) :=
        match n return (P n) with
        | O => p0
        | S n' => step n' (rec n')
        end.

Definition addn0' : forall n : nat, n + 0 = n
:= @nat_ind
    (fun n => n + 0 = n)
    (erefl 0)
    (fun _ IHn => congr1 S IHn).

Definition nat_rect :
  forall (P : nat -> Type),
    P 0 ->
    (forall n : nat, P n -> P n.+1) ->
    forall n : nat, P n
  := fun P
         (p0 : P 0)
         (step : (forall n : nat, P n -> P n.+1)) =>
       fix rec (n : nat) :=
       match n return (P n) with
       | O => p0
       | S n' => step n' (rec n')
       end.

Definition addn' : nat -> nat -> nat
:=  @nat_rect
      (fun _ => nat -> nat)
      id
      (fun _ pn => succn \o pn).

Check erefl : addn' 20 15 = 35.









