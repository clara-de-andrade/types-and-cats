Require Import Coq.Init.Prelude.

(** * Booleans *)

(** An inductive boolean type. *)

Inductive Bool : Type :=
| True
| False.

(** Boolean operations: not, or, and, iff. *)

Definition not (p : Bool) : Bool :=
  match p with
  | True  => False
  | False => True
  end.

Definition and (p q : Bool) : Bool :=
  match p, q with
  | True  , True => True
  | _     , _    => False
  end.
Notation "p && q" := (and p q).

Definition or (p q : Bool) : Bool :=
  match p, q with
  | False, False => False
  | _    , _     => True
  end.
Notation "p || q" := (or p q).

Definition iff (p q : Bool) : Bool :=
  match p, q with
  | True , True  => True
  | False, False => True
  | _    , _     => False
  end.
Notation "p <> q" := (iff p q).

(** * Natural numbers *)

(** An inductive natural numbers type. *)

Inductive Nat : Type :=
| O : Nat
| S (n : Nat) : Nat.

(** Definitions of numerals. *)

Notation "0" := O.
Notation "1" := (S 0).
Notation "2" := (S 1).
Notation "3" := (S 2).
Notation "4" := (S 3).
Notation "5" := (S 4).

(** Boolean equality for [Nat]. *)

Fixpoint eq_nat (m n : Nat) : Bool :=
  match m, n with
  | 0   , 0    => True
  | 0   , S n' => False 
  | S m', 0    => False
  | S m', S n' => (eq_nat m' n')
  end.
Notation "m == n" := ((eq_nat m n) = True)
  (at level 30).
Notation "m != n" := ((eq_nat m n) = False)
  (at level 30).

(** [==] is reflexive: a simple proof by [simpl], [rewrite] and [reflexivity]. *)

Lemma eq_nat_ref : forall (n : Nat), n == n.
Proof.
  intros. induction n as [ | n' IHn ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

(** * Lists (polymorphism) *)

(** A inductive and polymorphic list type. *)

Inductive List (X : Type) : Type :=
  | nil
  | cons (x : X) (xs : List X).

(** Type paremeter is implicit in the constructors. *)

Arguments nil {X}.
Arguments cons {X} x xs.

(** Basic syntax sugar for lists. *)

Notation "[]" := nil.
Notation "x :: xs" := (cons x xs)
  (at level 60, right associativity).
Notation "[ x , .. , y ]" := (x :: .. (y :: nil) ..).

(** Some basic list predicates and operations. *)

Definition null {X : Type} (l : List X) : Bool :=
  match l with
  | []     => True
  | _ :: _ => False
  end.

Fixpoint length {X : Type} (l : List X) : Nat :=
  match l with
  | []      => 0
  | _ :: xs => S (length xs)
  end.

Fixpoint append {X : Type} (l l' : List X) : List X :=
  match l with
  | []      => l'
  | x :: xs => x :: (append xs l')
  end.
Notation "l1 ++ l2" := (append l1 l2)
  (at level 60, right associativity).

Fixpoint map {X Y : Type} (f : X -> Y) (l : List X) : List Y :=
  match l with
  | []      => []
  | x :: xs => (f x) :: (map f xs)
  end.

Fixpoint filter {X : Type} (pred : X -> Bool) (l : List X) : List X :=
  match l with
  | []      => []
  | x :: xs => if (pred x)
               then x :: (filter pred xs)
               else (filter pred xs)
  end.

(** Theorems for free. *)

Lemma append_cons : forall {X : Type} (x : X) (xs : List X),
  x :: xs = [x] ++ xs.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma append_nil_l_l : forall {X : Type} (l : List X), [] ++ l = l.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma append_l_nil_l : forall {X : Type} (l : List X),
                       l ++ [] = l.
Proof.
  induction l as [ | x xs Hl ].
  - simpl. reflexivity.
  - simpl. rewrite -> Hl. reflexivity.
Qed.

Lemma append_assoc : forall {X : Type} (l m n : List X),
  l ++ (m ++ n) = (l ++ m) ++ n.
Proof.
  intros. induction l as [ | x xs Hn ].
  - simpl. reflexivity.
  - simpl. rewrite -> Hn. reflexivity.
Qed.