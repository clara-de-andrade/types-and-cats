From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives.

(** TODO: document *)


(* map composition *)
Definition comp (A B C : Type) (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x).

(* standard notation *)
Notation "g ∘ f" :=
  (comp _ _ _ f g)
  : core_scope.


(* identity map *)
Definition id (A : Type) : A -> A := fun x => x.

(* type paramater is inferred from context *)
Arguments id {A}.


(* projection maps from Sigma types *)

Definition fst {A : Type} {P : A -> Type}
  (p : ∑ (x : A), P x) : A :=
  match p with
  | (a, b) => a
  end.

Definition snd {A : Type} {P : A -> Type} 
  (p : ∑ (x : A), P x) : P (fst p) :=
  match p with
  | (a, b) => b
  end.


(* induction for Unit type *)

Example Unit_rect_ex :
  forall {P : Unit -> Type} (p : P tt),
  exists (f : Π (u : Unit), P u),
  f tt = p.
Proof.
  intros. exists (Unit_rect P p).
  simpl. reflexivity.
Qed.


(* induction for Nat type *)

Example Nat_rect_ex :
  forall {P : ℕ -> Type}
         (a : P 0) (h : Π (n : ℕ), (P n -> P (S n))),
  exists (f : Π (n : ℕ), P n),
  (f 0 = a) ∧ (forall (n : ℕ), f (S n) = h n (f n)).
Proof.
  intros.
  exists (Nat_rect P a h).
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


(* induction for Id type *)

Example Id_rect_ex :
  forall {A : Type} {P : Π (x y : A) (p : x ~> y), Type}
         (g : Π (x : A), P x x (ref x)),
  exists (f : Π (x y : A) (p : x ~> y), P x y p),
  forall (x : A), (f x x (ref x)) = g x.
Proof.
  intros.
  exists (Id_rect A P g). simpl. reflexivity.
Qed.