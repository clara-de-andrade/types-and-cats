From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives.
From TypesAndCats Require Import Types.

(** TODO: document *)


Definition ap {A B : Type} {a b : A}
  (f : A -> B) (p : a ~> b)
  : (f a) ~> (f b) :=
  match p with
  | ref x => ref (f x)
  end.

Definition transport
  {A : Type} (P : A -> Type)
  {a b : A} (p : a ~> b)
  : P(a) -> P(b) :=
  match p with
  | ref x => id
  end.
Notation "p *" := (transport _ p)
  (at level 3).

Definition apd {A : Type} {P : A -> Type}
  (f : Π (x : A), P x) {a b : A} (p : a ~> b)
  : p* (f a) ~> (f b) :=
  match p with
  | ref x => ref (f x)
  end.


Example apd_ref {A : Type} {a b : A} (p : a ~> b)
  : p* (ref a) ~> (ref b) :=
  apd ref p.


Definition sym {A : Type} {a b : A} (p : a ~> b) : b ~> a :=
  match p with
  | ref x => ref x
  end.
Notation "p ^-1" :=
  (sym p).

Example sym_ref {A : Type} {x : A} : (ref x)^-1 = ref x.
Proof.
  intros. simpl. reflexivity.
Qed.

Example ap_sym {A : Type} {a b : A} (p q : a ~> b)
  : p ~> q -> p^-1 ~> q^-1 :=
  ap (fun p => p^-1).

Lemma sym_uniq {A : Type} {a b : A} (p : a ~> b)
  : (p^-1)^-1 ~> p.
Proof.
  intros. induction p.
  simpl. apply ref.
Qed.


Example eucl_l {A : Type} {a b : A} (p : a ~> b)
  : forall c : A, c ~> a -> c ~> b :=
  fun c => transport (fun x => c ~> x) p.

Example eucl_r {A : Type} {a b : A} (p : a ~> b)
  : forall c : A, a ~> c -> b ~> c :=
  fun c => transport (fun x => x ~> c) p.

Definition tr {A : Type} {a b c : A}
  (p : a ~> b) (q : b ~> c) : a ~> c :=
  transport (fun x => x ~> c) p^-1 q.
Notation "p • q" :=
  (tr p q)
  : core_scope.

Example tr_ref {A : Type} {x : A} : (ref x • ref x) = ref x.
Proof.
  intros.
  unfold tr.
  apply sym_ref.
Qed.


Lemma ap_tr_p {A : Type} {a b c : A}
  (p : a ~> b) (q q' : b ~> c)
  : q ~> q' -> p • q ~> p • q'.
Proof.
  intros H.
  apply (ap (fun q => p • q) H).
Qed.

Lemma ap_tr_l {A : Type} {a b c : A}
  (p p' : a ~> b) (q : b ~> c)
  : p ~> p' -> p • q ~> p' • q.
Proof.
  intros H.
  apply (ap (fun p => p • q) H).
Qed.

Lemma ap_tr {A : Type} {a b c : A}
  (p p' : a ~> b) (q q' : b ~> c)
  : p ~> p' -> q ~> q' -> p • q ~> p' • q.
Proof.
  intros H1 H2.
  apply (ap_tr_l p p' q H1).
Qed.


Lemma sym_canc {A : Type} {a b : A} (p q : a ~> b)
  : p^-1 ~> q^-1 -> p ~> q.
Proof.
  Admitted.


Lemma ref_unit_l :
  forall {A : Type} {x y : A} (p : x ~> y), ref x • p ~> p.
Proof.
  Admitted.