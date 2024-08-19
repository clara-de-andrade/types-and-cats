From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives.

(** TODO: document *)

(* TODO: explain *)

Definition id {A : Type} : A -> A :=
  fun (x : A) => x.

Lemma id_unit_r {A B : Type} (f : A -> B) : (f ∘ id) = f.
Proof.
  intros. reflexivity.
Qed.

Lemma id_unit_l {A B : Type} (f : A -> B) : (id ∘ f) = f.
Proof.
  intros. reflexivity.
Qed.


(** Dizemos que [fst] é a primeira projeção, e que [snd] é a segunda projeção,
    do tipo [∑ (x : A), P x]. Ou seja, se [p : ∑ (x : A), P x] é um par, então
    [fst p : A] e [snd p : P (fst p)]. Em particular, se [p : A × B], então
    [fst p : A] e [snd p : B]. Portanto, [fst] e [snd] "extraem" ambos os
    componentes de um par. *)

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


(** Note que, pela definição indutiva de [Unit], existe um termo [Unit_rect]
    onde, para todo [P : Unit -> Type], se [p : P tt], então existe um mapa
    [f : Π (x : Unit), P x] tal que [f tt = p], onde [f = Unit_rect P p]. *)

Example Unit_rect_ex :
  forall {P : Unit -> Type} (p : P tt),
  exists (f : Π (u : Unit), P u),
  f tt = p.
Proof.
  intros. exists (Unit_rect P p).
  simpl. reflexivity.
Qed.


(** Novamente, pela definição indutiva de [ℕ], existe um termo [Nat_rect] onde,
    para todo [P : ℕ -> Type], se [a : P 0] e [h : Π (n : ℕ), (P n -> P (S n))]
    então existe um mapa [f : Π (n : ℕ), P n] tal que [f 0 = a] e, se [n : ℕ],
    então [f (S n) = h n (f n)], onde [f = Nat_rect P a h]. *)

Example Nat_rect_ex :
  forall {P : ℕ -> Type}
         (a : P 0) (h : Π (n : ℕ), (P n -> P (S n))),
  exists (f : Π (n : ℕ), P n),
  (and (f 0 = a) (forall (n : ℕ), f (S n) = h n (f n))).
Proof.
  intros.
  exists (Nat_rect P a h).
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


(* TODO: explain *)

Example Id_rect_ex :
  forall {A : Type} {P : Π (x y : A) (p : x ~> y), Type}
         (g : Π (x : A), P x x (ref x)),
  exists (f : Π (x y : A) (p : x ~> y), P x y p),
  forall (x : A), (f x x (ref x)) = g x.
Proof.
  intros.
  exists (Id_rect A P g). simpl. reflexivity.
Qed.