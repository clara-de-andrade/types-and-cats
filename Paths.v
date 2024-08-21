From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives Types.


(** TODO: document *)

Instance Id_reflexive (A : Type) : Reflexive (@Id A).
Proof.
  exact ref.
Defined.


Definition ap {A B : Type} (f : A -> B)
  {a b : A} (p : a ~> b)
  : (f a) ~> (f b) :=
  match p with
  | ref x => ref (f x)
  end.

Lemma ap_ref {A B : Type} (f : A -> B) {a : A}
  : ap f (ref a) = ref (f a).
Proof.
  simpl. reflexivity.
Qed.


Definition transport
  {A : Type} (P : A -> Type)
  {a b : A} (p : a ~> b)
  : P(a) -> P(b) :=
  match p with
  | ref x => id
  end.

Notation "p *" := (transport _ p)
  (at level 3).

Lemma transport_ref {A : Type} (P : A -> Type) {a : A} (u : P a)
  : (transport P (ref a) u) = u.
Proof.
  simpl. reflexivity.
Qed.


Definition apd {A : Type} {P : A -> Type}
  (f : Π (x : A), P x) {a b : A} (p : a ~> b)
  : p* (f a) ~> (f b) :=
  match p with
  | ref x => ref (f x)
  end.


Example apd_ref {A : Type} {a b : A} (p : a ~> b)
  : p* (ref a) ~> (ref b) :=
  apd ref p.


Definition sym {A : Type} (a b : A) (p : a ~> b) : b ~> a.
Proof.
  induction p.
  reflexivity.
Defined.

Notation "p ^-1" :=
  (sym _ _ p)
  : core_scope.

Instance Id_symmetric (A : Type) : Symmetric (@Id A).
Proof.
  exact sym.
Defined.


Example sym_ref {A : Type} {x : A} : (ref x)^-1 = ref x.
Proof.
  simpl. reflexivity.
Qed.

Example ap_sym {A : Type} {a b : A} (p q : a ~> b)
  : p ~> q -> p^-1 ~> q^-1 :=
  ap (fun p => p^-1).


Definition tr {A : Type} (a b c : A)
  (p : a ~> b) (q : b ~> c) : a ~> c.
Proof.
  induction p, q.
  reflexivity.
Defined.

Notation "p • q" :=
  (tr _ _ _ p q)
  : core_scope.
  
Instance Id_transitive (A : Type) : Transitive (@Id A).
Proof.
  exact tr.
Defined.


Example eucl_l {A : Type} (a b c : A)
  (p : a ~> c) (q : b ~> c) : a ~> b.
Proof.
  induction p, q.
  reflexivity.
Qed.

Example eucl_r {A : Type} (a b c : A)
  (p : a ~> b) (q : a ~> c) : b ~> c.
Proof.
  induction p, q.
  reflexivity.
Qed.


Example tr_ref {A : Type} {x : A} : (ref x • ref x) = ref x.
Proof.
  intros. unfold tr.
  simpl. reflexivity.
Qed.


Lemma ap_tr_l {A : Type} {a b c : A}
  (p p' : a ~> b) (q : b ~> c)
  : p ~> p' -> p • q ~> p' • q.
Proof.
  intros H.
  apply (ap (fun p => p • q) H).
Qed.

Lemma ap_tr_r {A : Type} {a b c : A}
  (p : a ~> b) (q q' : b ~> c)
  : q ~> q' -> p • q ~> p • q'.
Proof.
  intros H.
  apply (ap (fun q => p • q) H).
Qed.

Lemma ap_tr_lr{A : Type} {a b c : A}
  (p p' : a ~> b) (q q' : b ~> c)
  : p ~> p' -> q ~> q' -> p • q ~> p' • q.
Proof.
  intros H1 H2.
  apply (ap_tr_l p p' q H1).
Qed.


Lemma ref_unit_l {A : Type} {a b : A} (p : a ~> b)
  : ref a • p ~> p.
Proof.
  induction p.
  reflexivity.
Qed.

Lemma ref_unit_r {A : Type} {a b : A} (p : a ~> b)
  : p • ref b ~> p.
Proof.
  induction p.
  reflexivity.
Qed.

Lemma ref_unit {A : Type} {a b : A} (p : a ~> b)
  : and (ref a • p ~> p) (p • ref b ~> p).
Proof.
  split.
  - apply ref_unit_l.
  - apply ref_unit_r.
Qed.

Lemma tr_assoc {A : Type} {a b c d : A}
  (p : a ~> b) (q : b ~> c) (r : c ~> d) :
  p • (q • r) ~> (p • q) • r.
Proof.
  induction p, q, r.
  reflexivity.
Qed.

Lemma sym_uniq {A : Type} {a b : A} (p : a ~> b)
  : (p^-1)^-1 ~> p.
Proof.
  induction p.
  simpl. reflexivity.
Qed.


Lemma ref_ap {A B : Type} (f : A -> B)
  : forall x : A, (ap f (ref x)) ~> ref (f x).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Lemma sym_ap {A B : Type} (f : A -> B) {a b : A} (p : a ~> b)
  : (ap f p^-1) ~> (ap f p)^-1.
Proof.
  induction p.
  simpl. reflexivity.
Qed.

Lemma tr_ap  {A B : Type} (f : A -> B)
  {a b c : A}  (p : a ~> b) (q : b ~> c)
  : ap f (p • q) ~> (ap f p) • (ap f q).
Proof.
  induction p, q.
  simpl. reflexivity.
Qed.

Lemma id_ap {A B : Type} {a b : A} (p : a ~> b)
  : (ap id p) ~> p.
Proof.
  induction p.
  simpl. reflexivity.
Qed.

Lemma comp_ap {A B C : Type} (f : A -> B) (g : B -> C)
{a b : A} (p : a ~> b)
  : ap (g ∘ f) p ~> ap g (ap f p).
Proof.
  induction p.
  simpl. reflexivity.
Qed.


Definition transportconst
  {A : Type} (B : Type)
  {a b : A} (p : a ~> b) (y : B)
  : transport (fun x => B) p y ~> y :=
  match p with
  | ref x => ref y
  end.

Lemma apd_transportconst_ap
  {A B : Type} (f : A -> B)
  {a b : A} (p : a ~> b)
  : (apd f p) ~> (transportconst B p (f a)) • (ap f p).
Proof.
  induction p.
  simpl. reflexivity.
Qed.


(* TODO: learn how to make tactics to simplify these proofs *)

Lemma sym_inj {A : Type} {a b : A} (p q : a ~> b)
  : p^-1 ~> q^-1 -> p ~> q.
Proof.
  intro H.
  apply tr with (p^-1)^-1.
  - apply sym.
    apply sym_uniq.
  - apply tr with (q^-1)^-1.
    + apply ap_sym in H.
      apply H.
    + apply sym_uniq.
Qed.

(* TODO: sym_canc_l, sym_canc_r, unit_uniq *)


Theorem Sigma_path_ind {A : Type} {P : A -> Type} (w w' : ∑ (x : A), P x)
  : ∑ (p : (fst w) ~> (fst w')), (p* (snd w) ~> (snd w')) -> w ~> w'.
Proof.
  induction w as [a u].
  induction w' as [b v].
  simpl.

  intros r.
  destruct r as [p q].

  induction p as [a].  
  rewrite -> transport_ref in q.

  induction q as [u].
  reflexivity.
Qed.

Definition lift {A : Type} {P : A -> Type} {a b : A}
  (u : P a) (p : a ~> b) : (a, u) ~> (b, p* u).
Proof.
  apply Sigma_path_ind.
  exists p. simpl. reflexivity.
Defined.
