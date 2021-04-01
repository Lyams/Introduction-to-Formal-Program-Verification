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
