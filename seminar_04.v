From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom replace_with_your_solution_here : forall {A : Type}, A.



(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= replace_with_your_solution_here.


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= replace_with_your_solution_here.


(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= replace_with_your_solution_here.


(** * Exercise *)
Definition false_eq_true_implies_False :
  forall n, n.+1 = 0 -> False
:= fun n => fun Sn_eq0 : n.+1 = 0 =>
  match
    Sn_eq0 in (_ = z) return (if z is z'.+1
      then True else False)
  with
  | erefl => I
  end.

Print nat_ind.
(** * Exercise *)
Definition addnS (m n : nat) :
           m + n.+1 = (m + n).+1
:= (nat_ind (fun m => m + n.+1 = (m + n).+1)
    (erefl n.+1)
    (fun m' addnS' => congr1 (fun x => x.+1) addnS' )) m.

Definition addnS'' :
  forall m n, m + n.+1 = (m + n).+1
:= fix addnS'' m n :=
  match m as m return m + n.+1 = (m + n).+1 with
  | 0 => erefl n.+1
  | m'.+1 =>
    let prevH : m' + n.+1 = (m' + n).+1 := addnS'' m' n in
      let currH : (m' + n.+1).+1 = ((m' + n).+1 ).+1 :=
          congr1 (fun x => x.+1) prevH
     in currH end.

Print congr1.
About congr1.

(** * Exercise *)
Definition addA : associative addn
:= fix addA (b c d : nat) {struct b} : b + (c + d) = b + c + d
:= ( nat_ind (fun b => b + (c + d) = b + c + d)
      (erefl (c + d) )
      (fun b' addA' => congr1 (fun z => z.+1) addA')
    ) b.


(** * Exercise: *)

Print congr1.
Print etrans.
Print eq_trans.
About left_commutative.
Print left_commutative.
Print eq_sym.
(*Definition addnCA : left_commutative addn
:= fix fa (b c d : nat) {struct b} : b + (c + d) = c + (b + d)
  := match b return (b + (c + d) = c + (b + d)) with
      | 0 => erefl (c+d)
      | b'.+1 => 
        let H1 (*:  b'.+1 + ( c + d) = c.+1 + (b' + d) *) := congr1 S (fa b' c d) in
        let S (* : c.+1 + (b' + d) = c + (b'.+1 + d) *) := eq_sym (addnS c.+1 (b' + d)) in
        eq_trans H1 S
      end. *)

(*( nat_ind (fun b => b + (c + d) = c + (b + d))
        (erefl (c+d))
        (fun (b' : nat) addnCA' => _ addnCA' )
    ) b. *)

Print commutative.
Print eq_refl.
Print addn.
(** * Exercise (optional): *)
Definition addnC : commutative addn
:= fix addnC' (x y : nat)
:= match x  with
  | O => erefl _
  | b'.+1 => _
  end.

(*Definition addnC : commutative addn
:= fix addnC' (x y : nat) := (nat_ind 
    (fun x => x + y = y + x)
    (_ y)
    (fun (x' : nat) addnC' => congr1  (fun z => z.+1) addnC' )
    ) x.
*)

(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)


(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= replace_with_your_solution_here.