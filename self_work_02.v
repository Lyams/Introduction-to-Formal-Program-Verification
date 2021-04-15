Inductive unit : Set := tt.
Check tt.
Check unit.

Inductive empty : Set := .
Check empty.

From mathcomp
Require Import ssreflect ssrbool.

Print bool.

Definition negate b := 
  match b with 
  | true  => false
  | false => true
  end.

Check negate.
Print nat.

From mathcomp
Require Import ssrnat.

Fixpoint my_plus n m := 
 match n with 
 | 0     => m   
 | n'.+1 => let: tmp := my_plus n' m
            in tmp.+1
 end.
From mathcomp Require Import seq.
Print seq.

Eval compute in my_plus 5 7.

Search "ﬁlt" ( _ -> list _).

Search _ ((?X -> ?Y) -> _ ?X -> _ ?Y).

Search _ (_ * _ : nat).

Search _ (_ * _: Type).


 