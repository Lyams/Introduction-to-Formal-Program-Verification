(* По видео
Кузнецов С.Л. Coq: построение и проверка математических доказательств на компьютере (22.04.2020)
: https://www.youtube.com/watch?v=D6sdE3FVlcY *)

Variable A B C : Prop.

Theorem syll : (A -> B) -> ((B -> C) -> (A -> C)).
Proof.
intro.
intro.
intro.
apply H0.
apply H.
assumption.
Qed.

Theorem syll' : (A -> B) -> ((B -> C) -> (A -> C)).
Proof.
auto.
Qed.