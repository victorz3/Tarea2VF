(* Script de ejercicios de lógica minimal. *)

(* Ejercicio 1a *)
Theorem triple_neg_single: forall (a: Prop), ~~~a <-> ~a.
Proof.
split.
+ unfold not.
  intros.
  apply H.
  intro.
  apply H1.
  trivial.
+ unfold not.
  intros.
  apply H0.
  intro.
  apply H; trivial.
Qed.

(* Ejercicio 1b *)
Theorem double_neg_and: forall (a b: Prop), ~~(a/\b) -> ~~a /\ ~~b.
Proof.
unfold not.
intros.
split.
+ intro.
  apply H.
  intro.
  apply H0.
  destruct H1.
  trivial.
+ intro.
  apply H.
  intro.
  apply H0.
  destruct H1.
  trivial.
Qed.

(* Ejercicio 1c *)
Theorem double_neg_forall: forall (T:Type) (a: T -> Prop), ~~(forall x:T, a x) -> forall x:T, ~~a x.
Proof.
unfold not.
intros.
apply H.
intro.
apply H0.
apply H1.
Qed.


