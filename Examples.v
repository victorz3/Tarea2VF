Require Import Classical.
From src Require Export Props_LC.
From src Require Export Props_LI.
From src Require Export Props_LM.

(* Parte 5 de la tarea. *)

(* Lema auxiliar. El otro lado de Modus Tollens 
 * Propiedad de lógica clásica *)
Lemma modus_tollens_2: forall (A B: Prop), (~A -> ~B) -> (B -> A).
Proof.
intros.
assert (~~B -> ~~A).
+ apply modus_tollens.
  trivial.
+ assert (~~B).
  - apply double_neg_intro.
    trivial.
  - apply H1 in H2.
    apply NNPP.
    trivial.
Qed.

(* Ejercicio 5a 
 * Se usó lógica clásica. *)
Theorem fivea: forall (A B C D : Prop), (A -> B) /\ (~(A \/ C) -> D) /\
(A \/ B -> C) -> (~D -> C).
Proof.
intros.
destruct H.
destruct H1.
apply modus_tollens in H1.
+ apply NNPP in H1.
  destruct H1.
  - assert (A \/ B).
    * left; trivial.
    * apply H2; trivial.
  - trivial.
+ trivial.
Qed.

(* Ejercicio 5b
 * Se usó lógica clásica *)
Theorem fiveb: forall (A B C D: Prop), A \/ B -> (~D -> C) /\ (~B -> ~A) -> (C -> ~B) -> D.
Proof.
intros.
destruct H0.
destruct H.
+ assert (A -> B).
  - apply modus_tollens_2.
    trivial.
  - apply H3 in H.
    assert (B -> ~C).
    * apply modus_tollens_2.
      intro.
      apply NNPP in H4.
      apply H1.
      trivial.
    * apply H4 in H.
      assert (~C -> ~~D).
      ++ apply modus_tollens.
         trivial.
      ++ apply H5 in H.
         apply NNPP.
         trivial.
+ assert (B -> ~C).
  - apply modus_tollens_2.
    intro.
    apply H1.
    apply NNPP; trivial.
  - apply H3 in H.
    assert (~C -> D).
    * apply modus_tollens_2.
      intro.
      apply H0 in H4.
      apply double_neg_intro.
      trivial.
    * apply H4 in H.
      trivial.
Qed.


(* Ejercicio 5c 
 * Se utilizó lógica clásica (modus tollens).*)
Theorem fivec: forall (T: Type) (a: T) (P B R: T -> Prop),
(forall x:T, P x -> ~B x) -> R a -> (forall x: T, R x -> B x) -> ~P a.
Proof.
intros.
intro.
apply H in H2.
assert (forall x: T, ~B x -> ~R x).
+ intro.
  apply modus_tollens.
  apply H1.
+ apply H3 in H2.
  contradiction.
Qed.

(* Ejercicio 5d 
 * Se usó lógica clásica *)
Theorem fived: forall (T1: Type) (P B R S T: T1 -> Prop), 
(forall x:T1, P x \/ B x -> ~R x) /\ (forall x:T1, S x -> R x) -> (forall x:T1, P x -> ~S x \/ T x).
Proof.
intros.
destruct H.
assert (P x \/ B x).
+ left; trivial.
+ apply H in H2.
  assert (forall x:T1, ~R x -> ~S x).
  - intro.
    apply modus_tollens.
    apply H1.
  - left;apply H3.
    trivial.
Qed.

(* Ejercicio 5e 
 * La propiedad no se cumple para T vacío, por lo que agregamos la hipótesis
 * de que existe alguien en T. 
 * Se usó lógica minimal. *)
Theorem fivee: forall (T: Type) (x: T) (P B: T -> Prop),(forall x:T, P x /\ exists y:T, B y) -> (exists x:T, P x /\ B x).
Proof.
intros.
apply H in x.
destruct x.
exists x.
split.
+ apply H.
+ trivial.
Qed.

(* Ejercicio 5f
 * Se usó lógica minimal *)
Theorem fivef: forall (T1 T2: Type) (P: T1 -> Prop) (R: T1 -> T2 -> Prop), 
(forall x:T1, exists y:T2, P x -> R x y) -> (forall x:T1, P x -> exists y:T2, R x y).
Proof.
intros.
assert (exists y:T2, P x -> R x y).
+ apply H.
+ destruct H1.
  exists x0.
  apply H1; trivial.
Qed.

(* Ejercicio 5g 
 * Se usó lógica minimal.*)
Theorem fiveg: forall (T : Type) (P B: T -> Prop), 
(forall x:T, P x -> ~B x) -> (~exists x:T, P x /\ B x).
Proof.
intros.
intro.
destruct H0.
destruct H0.
apply H in H0.
apply H0.
trivial.
Qed.

(* Ejercicio 5h 
 * Se usó lógica minimal. *)
Theorem fiveh: forall (T1 T2: Type) (P: T1 -> T2 -> Prop), 
(exists x:T1, forall y:T2, P x y) -> (forall y:T2, exists x:T1, P x y).
Proof.
intros.
destruct H.
exists x.
apply H.
Qed.

