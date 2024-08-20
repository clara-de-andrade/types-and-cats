From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives Types Paths.


(** TODO: document *)

Definition homotopy {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) : Type
  := Π (x : A), (f x ~> g x).
Infix "~" := homotopy
  (at level 99)
  : core_scope.

Example homotopy_ref {A : Type} {P : A -> Type}
  (f : Π (x : A), P x) : f ~ f :=
  fun x => ref (f x).

Example homotopy_sym {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) (alph : f ~ g) : g ~ f :=
  fun x => (alph x)^-1.

Example homotopy_tr {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) (alph : f ~ g) (beta : g ~ h) : f ~ h :=
  fun x => (alph x) • (beta x). 


Definition homotopy_comp {A B C : Type}
  (f f' : A -> B) (g g' : B -> C)
  (alph : f ~ f') (beta : g ~ g') : g ∘ f ~ g' ∘ f' :=
  fun x => beta (f x) • (ap g' (alph x)).
Infix "·" := homotopy_comp
  (at level 99)
  :  core_scope.

Example homotopy_comp_l {A B C : Type}
  (f f' : A -> B) (g : B -> C)
  (alph : f ~ f') : g ∘ f ~ g ∘ f' :=
  homotopy_comp f f' g g alph (homotopy_ref g).

Example homotopy_comp_r {A B C : Type}
  (f : A -> B) (g g' : B -> C)
  (beta : g ~ g') : g ∘ f ~ g' ∘ f :=
  homotopy_comp f f g g' (homotopy_ref f) beta.


(* TODO: unfold proof *)
Theorem homotopy_naturality {A B : Type}
  (f g : A -> B) (eta : f ~ g)
  {a b : A} (p : a ~> b)
  : (eta a) • (ap g p) ~> (ap f p) • (eta b).
Proof.
  induction p. simpl.
  apply ref_unit_r.
Qed.


Definition logeqv (A B : Type) : Type
  := (A -> B) × (B -> A).
Infix "<->" := logeqv
  : type_scope.

Example logeqv_ref (A : Type) : A <-> A := (id, id).

Example logeqv_sym (A B : Type) : (A <-> B) -> (B <-> A) :=
  fun e => match e with  (f, g) => (g, f) end.

Example logeqv_tr (A B C : Type) : (A <-> B) -> (B <-> C) -> (A <-> C) :=
  fun e1 e2 => match e1, e2 with (f, f'), (g, g') => (g ∘ f, f' ∘ g') end.


Definition qinv {A B : Type} (f : A -> B) : Type
  := ∑ (g : B -> A), ((g ∘ f ~ id) × (f ∘ g ~ id)).

Definition isequiv {A B : Type} (f : A -> B) : Type
  := (∑ (g : B -> A), (g ∘ f ~ id)) × (∑ (g : B -> A), (f ∘ g ~ id)).

Definition homotopy_eqv (A B : Type) : Type :=
  ∑ (f : A -> B), isequiv f.
Infix "≃" := homotopy_eqv
  : type_scope.


Lemma qinv_logeqv_isequiv {A B : Type} (f : A -> B) :
  qinv f <-> isequiv f.
Proof.
  (* TODO: prove *)
Admitted.