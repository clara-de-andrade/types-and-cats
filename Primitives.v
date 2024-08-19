From HoTT Require Import Basics.

(** Apresentamos a seguir os elementos de uma simples teoria dos tipos
  axiomática capaz de formular as noções que veremos ao longo destas
  anotações e deduzir as suas consequências formais. *)

(** * Mapas *)

(** [A -> B] é o tipo dos _mapas_ de [A : Type] até [B : Type], onde um mapa
    [f : A -> B] deste tipo é apenas uma designação de exatamente um termo
    [f x : B] para todo termo [x : A]. De modo mais geral, para todo
    [A : Type] e [P : A -> Type], [Π (x : A), P x] é o tipo dos mapas
    _dependentes_ de [x : A] até [P x : Type], onde [f x : P x] para todo
    [x : A]. Podemos ainda considerar [A -> B] como um caso especial de
    [Π (x : A), P x], onde [P x = B] para todo [x : A].

    Em adição, se [t : P x] para todo [x : A], então o termo [fun x => t]
    é um mapa do tipo [Π x : A, P x] onde, se [a : A], então
    [(fun x => t) a = \[x := a\]t]. Dizemos que o termo [fun x => t] é um
    _mapa anônimo_. Em particular, temos que [f = (fun x (f x))] para todo mapa
    [f : Π (x : A), P]—ou seja, todo mapa é identico a um termo-#&lambda;#. *)

Notation "'Π' x .. y , P" :=
  (forall x, .. (forall y, P) ..)
  (at level 60, x binder, y binder, right associativity)
  : type_scope.

Notation "A -> B" :=
  (Π (_ : A), B)
  : type_scope.


(* TODO: explain *)

Definition comp {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun (x : A) => g (f x).

Notation "g ∘ f" :=
  (comp f g)
  : core_scope.

Lemma comp_assoc {A B C D : Type}
  (f : A -> B) (g : B -> C) (h : C -> D)
  : (h ∘ (g ∘ f)) = ((h ∘ g) ∘ f).
Proof.
  intros. reflexivity.
Qed.


(** * Pares *)

(** [A × B] é o tipo dos _pares_ de [A : Type] e [B : Type], onde um par
    deste tipo é um termo [(a, b) : A × B] tal que [a : A] e [b : B]. De
    modo mais geral, [A : Type] e [P : A -> Type], [∑ (x : A), P x] é o tipo
    dos pares _dependentes_ de [P] sobre [A], onde um par deste tipo é um
    termo [(a, b) : ∑ (x : A), P x] tal que [a : A] e [b : P a]. *)

Inductive Sigma {A : Type} (P : A -> Type) : Type :=
| pair (a : A) (b : P a) : Sigma P.
Arguments pair {A} {P}.

Notation "'∑' x .. y , P" :=
  (Sigma (fun x => .. (Sigma (fun y => P)) ..))
  (at level 60, x binder, y binder, right associativity)
  : type_scope.

Notation "A × B" :=
  (∑ (_ : A), B)
  : type_scope.

Notation "( x , y , .. , z )" :=
  (pair .. (pair x y) .. z).


(** * O tipo terminal *)

(** [Unit] é um tipo _unitário_, ou _terminal_. Em particular, [Unit] é um tipo
    indutivo cujo único construtor é [tt : Unit]. Como provaremos, [tt] é o
    único termo deste tipo, e [Unit] é o único tipo com exatamente um termo. *)

Inductive Unit : Type :=
| tt : Unit.


(** * Números naturais *)

(** [ℕ] é o tipo dos números naturais, onde [O : ℕ] é o número zero e [S n : ℕ]
    é o sucessor imediato do número [n : ℕ]. Os numerais '0', '1', '2', ...
    podem ser definidos inteiramente em termos de [O] e [S], por indução.
    Primeiro, [0] é definido como [O], e para todo numeral 'n', se [n : ℕ] é
    seu termo correspondente, então 'n + 1' é definido como [S n]. Em
    particular, '1' é definido como [S O], '2' é definido por [S 1], e assim
    por diante. Faremos apenas algumas destas definições por conveniência. *)

Inductive Nat : Type :=
| O : Nat
| S (n : Nat) : Nat.
Notation "'ℕ'" := Nat
  : type_scope.

Notation "0" := O.
Notation "1" := (S 0).
Notation "2" := (S 1).
Notation "3" := (S 2).
Notation "4" := (S 3).
Notation "5" := (S 4).


(** * Igualdades *)

(* TODO: explain *)

Inductive Id {A : Type} : A -> A -> Type :=
| ref (a : A) : Id a a.
Infix "~>" := Id
  (at level 99)
  : core_scope.

