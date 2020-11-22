(* Definiciones de lógica clásica. *)

Definition cotenability (A B:Prop) := ~(A -> ~ B).

Notation "A ° B" := (cotenability A B) (at level 60).