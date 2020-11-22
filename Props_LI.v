(* Parte 2 de la tarea: Lógica intuicionista. *)

(* Ejercicio 2a *)
Theorem double_neg_impl: forall (a b : Prop), ~~(a -> b) -> ~~a -> ~~b.
Proof.
unfold not.
intros.
apply H; intro.
apply H0; intro.
apply H1.
apply H2.
trivial.
Qed.

(* Ejercicio 2b *)
Theorem impl_double_neg: forall (a b: Prop), (~~a -> ~~b) -> ~~(a -> b).
Proof.
unfold not.
intros.
apply H0.
intro.
exfalso.
apply H.
+ intro.
  apply H2.
  trivial.
+ intro.
  apply H0.
  intro.
  trivial.
Qed.

(* Ejercicio 2 *)
Theorem impl_double_neg_iff: forall (a b: Prop), ~~(a -> b) <-> (~~a -> ~~b).
Proof.
split.
+ apply double_neg_impl.
+ apply impl_double_neg.
Qed.

