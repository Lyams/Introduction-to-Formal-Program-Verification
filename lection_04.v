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