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