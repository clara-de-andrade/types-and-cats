From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives Types Paths.


(** TODO: document *)


(* type of homotopies between maps *)
Definition homotopy {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) : Type
  := Π (x : A), (f x ~> g x).
Infix "~" := homotopy
  (at level 99)
  : core_scope.

(* identity homotopy *)
Definition hom_id {A : Type} {P : A -> Type}
  (f : Π (x : A), P x) : f ~ f :=
  fun x => ref (f x).

(* reflexivity of ~ *)
Instance hom_ref (A : Type) (P : A -> Type)
  : Reflexive (@homotopy A P).
Proof.
  exact hom_id.
Defined.


(* inverse of a homotopy *)
Definition hom_inv {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) (alph : f ~ g) : g ~ f :=
  fun x => (alph x)^-1.

(* symmetry of ~ *)
Instance hom_sym (A : Type) (P : A -> Type)
  : Symmetric (@homotopy A P).
Proof.
  exact hom_inv.
Defined.


(* vertical composition of homotopies *)
Definition hom_comp {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) (alph : f ~ g) (beta : g ~ h) : f ~ h :=
  fun x => (alph x) • (beta x).

(* transitivity of ~ *)
Instance hom_tr (A : Type) (P : A -> Type)
  : Transitive (@homotopy A P).
Proof.
  exact hom_comp.
Defined.


(* ~ is left-euclidean *)
Definition hom_eucl_l {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) : f ~ g -> f ~ h -> g ~ h :=
  fun alph beta x => (alph x)^-1 • (beta x).

(* ~ is right-euclidean *)
Definition hom_eucl_r {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) : f ~ h -> g ~ h -> f ~ g :=
  fun alph beta x => (alph x) • (beta x)^-1.


(* ~ is a congruence wrt map composition *)
Definition hom_comp_lr {A B C : Type}
  (f f' : A -> B) (g g' : B -> C)
  (alph : f ~ f') (beta : g ~ g') : g ∘ f ~ g' ∘ f' :=
  fun x => beta (f x) • (ap g' (alph x)).

(* ~ is a congruence wrt right composition *)
Definition hom_comp_r {A B C : Type}
  (f : A -> B) (g g' : B -> C)
  (beta : g ~ g') : g ∘ f ~ g' ∘ f :=
  fun x => beta (f x).

(* ~ is a congruence wrt left composition *)
Definition hom_comp_l {A B C : Type}
  (f f' : A -> B) (g : B -> C)
  (alph : f ~ f') : g ∘ f ~ g ∘ f' :=
  fun x => ap g (alph x).

(* TODO: define whiskering, horizontal composition of homotopies *)


(* map composition is associative *)
Lemma comp_assoc {A B C D : Type}
  (f : A -> B) (g : B -> C) (h : C -> D)
  : (h ∘ (g ∘ f)) ~ ((h ∘ g) ∘ f).
Proof.
  unfold homotopy.
  intros x.

  unfold comp.
  reflexivity.
Qed.

(* [id] is a right unit wrt map composition *)
Lemma id_unit_r {A B : Type} (f : A -> B) : f ∘ id ~ f.
Proof.
  unfold homotopy.
  intros x.

  unfold comp.
  unfold id.
  reflexivity.
Qed.

(* [id] is a left unit wrt map composition *)
Lemma id_unit_l {A B : Type} (f : A -> B) : id ∘ f ~ f.
Proof.
  unfold homotopy.
  intros x.

  unfold comp.
  unfold id.
  reflexivity.
Qed.


(* composition [id ∘ id] is equal to map [id] *)
Lemma id_unit_id {A : Type} : @id A ∘ @id A ~ @id A.
Proof.
  unfold homotopy.
  intros x.

  unfold comp.
  unfold id.
  reflexivity.
Qed.

(* [id] is unique as right unit wrt map composition *)
Lemma id_unit_r_uniq (u : Π (X : Type), (X -> X))
  : (forall (A B : Type) (f : A -> B), f ∘ u A ~ f)
  -> forall X : Type, u X ~ @id X.
Proof.
  intros Hyp X.

  apply hom_eucl_l with (id ∘ u X).
  - apply id_unit_l.
  - apply Hyp.
Qed.

(* [id] is unique as left unit wrt map composition *)
Lemma id_unit_l_uniq (u : Π (X : Type), (X -> X))
  : (forall (A B : Type) (f : A -> B), u B ∘ f ~ f)
  -> forall X : Type, u X ~ @id X.
Proof.
  intros Hyp X.

  apply hom_eucl_l with (u X ∘ id).
  - apply id_unit_r.
  - apply Hyp.
Qed.


(* homotopies are natural transformations *)
Theorem hom_naturality {A B : Type}
  (f g : A -> B) (alph : f ~ g)
  {a b : A} (p : a ~> b)
  : alph a • ap g p ~> ap f p • alph b.
Proof.
  induction p. unfold ap.
  apply eucl_l with (c := alph a).
  - apply ref_unit_r.
  - apply ref_unit_l.
Qed.


(* TODO: type of logical equivalences *)
Definition leqv (A B : Type) : Type
  := (A -> B) × (B -> A).
Infix "<->" := leqv
  : type_scope.


(* identity logical equivalence *)
Definition leqv_id (A : Type) : A <-> A := (id, id).

(* <-> is reflexive *)
Instance leqv_ref : Reflexive leqv.
Proof.
  exact leqv_id.
Defined.


(* inverse of logical equivalence *)
Example leqv_inv (A B : Type) : (A <-> B) -> (B <-> A) :=
  fun e => match e with  (f, g) => (g, f) end.

(* <-> is symmetric *)
Instance leqv_sym : Symmetric leqv.
Proof.
  exact leqv_inv.
Defined.


(* composition of logical equivalences *)
Example leqv_comp (A B C : Type) : (A <-> B) -> (B <-> C) -> (A <-> C) :=
  fun e1 e2 => match e1, e2 with (f, f'), (g, g') => (g ∘ f, f' ∘ g') end.

(* <-> is transitive *)
Instance leqv_tr : Transitive leqv.
Proof.
  exact leqv_comp.
Defined.


(* type of quasi-inverses of a map *)
Definition qinv {A B : Type} (f : A -> B) : Type
  := ∑ (g : B -> A), ((g ∘ f ~ id) × (f ∘ g ~ id)).

(* h-prop that a map is a (homotopic) equivalence *)
Definition isequiv {A B : Type} (f : A -> B) : Type
  := (∑ (g : B -> A), (g ∘ f ~ id)) × (∑ (g : B -> A), (f ∘ g ~ id)).


(* canonical map from qinv f to isequiv f *)
(* := fun (g, (alph, beta)) => ((g, alph), (g, beta)) *)
Lemma qinv_to_isequiv {A B : Type} (f : A -> B) : qinv f -> isequiv f.
Proof.
  intros e.
  destruct e as [g p].
  destruct p as [alph beta].
  split.
  + exact (g, alph).
  + exact (g, beta).
Defined.

(* map from isequiv f to qinv f *)
(* fun ((g, alph), (h, beta)) => (g, (alph, beta')) *)
Lemma isequiv_to_qinv {A B : Type} (f : A -> B) : isequiv f ->  qinv f.
Proof.
  intros e.
  destruct e as [p q].
  destruct p as [g alph].
  destruct q as [h beta].

  assert (gamma : g ~ h).
  {
    apply hom_eucl_l with (g ∘ f ∘ h).
    - apply hom_tr with (g ∘ id).
      + apply hom_comp_l with (f := f ∘ h) (f' := id) (g := g).
        exact beta. 
      + apply id_unit_r.
    - apply hom_tr with (id ∘ h).
      + apply hom_comp_r with (f := h) (g := g ∘ f) (g' := id).
        exact alph.
      + apply id_unit_l.
  }
  assert (beta' : f ∘ g ~ id).
  {
    apply hom_tr with (f ∘ h).
    - apply hom_comp_l.
      exact gamma.
    - exact beta.
  }

  exists g. split.
  - exact alph.
  - exact beta'.
Defined.

(* qinv f and isequiv f are logically equivalent *)
Lemma qinv_iff_isequiv {A B : Type} (f : A -> B) : qinv f <-> isequiv f.
Proof.
  split.
  - apply qinv_to_isequiv.
  - apply isequiv_to_qinv.
Defined.


(* type of (homotopic) equivalences *)
Definition heqv (A B : Type) : Type :=
  ∑ (f : A -> B), isequiv f.
Infix "≃" := heqv
  : type_scope.


Declare Scope heqv_scope.
Open Scope heqv_scope.


(* identity equivalence *)
Definition heqv_id (A : Type) : A ≃ A.
Proof.
  exists id.
  apply qinv_to_isequiv.

  unfold qinv.
  exists id. split.
  - exact id_unit_id.
  - exact id_unit_id.
Defined.

(* ≃ is reflexive *)
Instance heqv_ref
  : Reflexive heqv.
Proof.
  exact heqv_id.
Defined.

(*  *)
Example heqv_ref_id {A : Type} : heqv_ref A = (id, ((id, ref), (id, ref))).
Proof.
Admitted.
(*
  unfold heqv_ref.
  unfold qinv_to_isequiv.
  reflexivity.
*)


Lemma heqv_sym (A B : Type) : A ≃ B -> B ≃ A.
Proof.
  intros e.
  destruct e as [f p].
  apply isequiv_to_qinv in p.
  destruct p as [f' [alph beta]].

  unfold heqv.
  exists f'.

  unfold isequiv.
  refine ((f, beta), (f, alph)).
Defined.

Notation "f ^-1" := (heqv_sym _ _ f)
  (at level 3)
  : heqv_scope.

Instance heqv_symmetric
  : Symmetric heqv.
Proof.
  exact heqv_sym.
Defined.

Example heqv_sym_id {A : Type} : (heqv_ref A)^-1 = heqv_ref A.
Proof.
(*
  unfold heqv_ref.
  unfold qinv_to_isequiv.

  unfold heqv_sym.
  unfold isequiv_to_qinv.

  unfold homotopy_tr.
  unfold homotopy_comp_l.
*)
Admitted.