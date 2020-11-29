Require Import Classical.

(* Importando definiciones. *)
From src Require Export Defs_LC.

(* Lema auxiliar, a -> ~~a *)
Lemma double_neg_intro: forall (a: Prop), a -> ~~a.
Proof.
intros.
assert (~~a \/ ~~~a).
+ apply classic.
+ destruct H0.
  - trivial.
  - apply NNPP in H0.
    contradiction.
Qed.

(* Lema auxiliar, a /\ ~b -> ~(a -> b) *)
Lemma and_to_imply: forall (a b: Prop), a /\ ~b -> ~(a -> b).
Proof.
intros.
destruct H.
contradict H0.
apply H0.
trivial.
Qed.

(* Lema auxiliar: Modus Tollens *)
Lemma modus_tollens: forall (a b: Prop), (a -> b) -> (~b -> ~a).
Proof.
intros.
contradict H0.
apply H.
trivial.
Qed. 

(* Lema auxiliar: Implicación de ~forall -> exists~ se cumple con dos variables *)
Lemma not_forall_exists_not_double: forall (U1 U2: Type) (P: U1 -> U2 -> Prop), 
~(forall (x: U1),forall (y: U2), P x y) -> exists (x: U1), exists (y: U2), ~P x y.
Proof.
intros.
assert (exists x: U1, ~ forall y:U2, P x y).
+ apply not_all_ex_not.
  trivial.
+ destruct H0.
  exists x.
  apply not_all_ex_not.
  trivial.
Qed.

(* Ejercicio 3a *)
Theorem coten_conm: forall (a b: Prop), a ° b <-> b ° a.
Proof.
unfold cotenability.
split.
+ intro.
  contradict H.
  intro.
  assert (b \/ ~b).
  * apply classic.
  * destruct H1.
    - apply H in H1.
      contradiction.
    - trivial.
+ intro.
  contradict H.
  intro.
  assert (a \/ ~a).
  * apply classic.
  * destruct H1.
    - apply H in H1.
      contradiction.
    - trivial.
Qed.

(* Ejercicio 3b *)
Theorem coten_assoc: forall (a b c: Prop), a ° (b ° c) <-> (a ° b) ° c.
Proof.
unfold cotenability.
split.
+ intro.
  contradict H.
  intro.
  apply double_neg_intro.
  intro.
  apply H.
  apply and_to_imply.
  split.
  - trivial.
  - apply double_neg_intro.
    trivial.
+ intro.
  contradict H.
  intro.
  contradict H0.
  intro.
  apply H in H1.
  apply NNPP in H1.
  apply imply_to_or in H1.
  destruct H1.
  - trivial.
  - contradiction.
Qed.

(* Ejercicio 3c *)
Theorem coten_distr: forall (A B C: Prop), (A ° B) \/ (A ° C) <-> A ° (B \/ C).
Proof.
unfold cotenability.
intros.
split.
+ intro.
  destruct H.
  - contradict H.
    intro.
    apply H in H0.
    apply not_or_and in H0.
    destruct H0.
    trivial.
  - contradict H.
    intro.
    apply H in H0.
    apply not_or_and in H0.
    destruct H0.
    trivial.
+ intro.
  apply imply_to_and in H.
  destruct H.
  apply NNPP in H0.
  destruct H0.
  - left.
    apply and_to_imply.
    split.
    * trivial.
    * apply double_neg_intro.
      trivial.
  - right.
    apply and_to_imply.
    split.
    * trivial.
    * apply double_neg_intro.
      trivial.
Qed.

(* Ejercicio 3d *)
Theorem coten_fusion: forall (A B C: Prop), (A -> B -> C) <-> ((A ° B) -> C).
Proof.
unfold cotenability.
split.
+ intros.
  apply imply_to_and in H0.
  destruct H0.
  apply H.
  * trivial.
  * apply NNPP.
    trivial.
+ intros.
  apply H.
  apply and_to_imply.
  split.
  * trivial.
  * apply double_neg_intro.
    trivial.
Qed.

(* Ejercicio 3e *)
Theorem imply_def: forall (A B C: Prop), (A -> B) <-> ~(A ° ~B).
Proof.
unfold cotenability.
split.
+ intro.
  apply double_neg_intro.
  intro.
  apply double_neg_intro.
  apply H.
  trivial.
+ intros.
  apply NNPP in H.
  apply H in H0.
  apply NNPP.
  trivial.
Qed.

(* Ejercicio 4a *)
Theorem foura: forall (T1: Type) (A B C: T1->Prop) (a: T1), ((exists x:T1, (A x /\ B x)) -> (forall x:T1, B x -> C x))
/\ (B a /\ ~ C a) -> ~(forall x:T1, A x).
Proof.
intros.
destruct H.
apply ex_not_not_all.
assert (B a /\ ~ C a); trivial.
apply and_to_imply in H0.
apply modus_tollens in H.
+ exists a.
  destruct H1.
  assert (forall x:T1, ~ (A x /\  B x)).
  - apply not_ex_all_not.
    exact H.
  - assert (~ (A a /\ B a)).
    * apply H3.
    * apply not_and_or in H4.
      destruct H4.
      ++ trivial.
      ++ contradiction.
+ apply ex_not_not_all.
  exists a.
  trivial.
Qed.


(* Ejercicio 4b *)
Theorem fourb: forall (T1 T2 T3: Type) (B : T1 -> T2 -> Prop) (m: T2) (C W : T3 -> Prop) (G: T1 -> T3 -> Prop), 
((exists x: T1, ~ (B x m) /\ forall y: T3, C y -> ~ G x y)
/\ (forall z: T1, ~ (forall y : T3, W y -> G z y) -> B z m)) -> forall x: T3, C x -> ~ W x.
Proof.
intros.
destruct H.
destruct H.
destruct H.
apply H2 in H0.
assert (forall z: T1, (exists y: T3, ~(W y -> G z y)) -> B z m).
+ intros.
  apply H1.
  apply ex_not_not_all.
  exact H3.
+ assert((exists y : T3, ~ (W y -> G x0 y)) -> B x0 m).
  - apply H3.
  - apply modus_tollens in H4.
    eapply not_ex_not_all in H4.
    apply modus_tollens in H4.
    apply H4.
    trivial.
    trivial.
Qed.


(* Ejercicio 4c *)
Theorem fourc: forall (T1 T3 T2 T4: Type) (P H : T1 -> Prop) (C: T1 -> Prop) (L: T3 -> Prop) (A: T1 -> T3 -> Prop) (R: T2 -> Prop) (B: T2 -> T4 -> Prop),
((~forall x: T1, ~ P x \/ ~ H x) -> (forall x: T1, C x /\ forall y: T3, L y -> A x y)) /\
((exists x:T1, H x /\ forall y: T3, L y -> A x y) -> (forall x: T2, R x /\ forall y:T4, B x y)) ->
((~forall x: T2, forall y: T4, B x y) -> forall x: T1, ~ P x \/ ~ H x).
Proof.
intros.
destruct H0.
apply not_forall_exists_not_double in H1.
destruct H1.
destruct H1.
apply modus_tollens in H2.
+ eapply not_ex_all_not in H2.
  apply not_and_or in H2.
  destruct H2.
  * right; apply H2.
  * apply modus_tollens in H0.
    - apply NNPP in H0.
      apply H0.
    - apply ex_not_not_all.
      apply not_all_ex_not in H2.
      destruct H2.
      exists x.
      apply or_not_and.
      right.
      apply ex_not_not_all.
      exists x2.
      trivial.
+ apply ex_not_not_all.
  exists x0.
  apply or_not_and.
  right.
  apply ex_not_not_all.
  exists x1; trivial.
Qed.


