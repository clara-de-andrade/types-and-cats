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
Instance homotopy_reflexive (A : Type) (P : A -> Type)
  : Reflexive (@homotopy A P).
Proof.
  exact homotopy_ref.
Defined.

Example homotopy_sym {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) (alph : f ~ g) : g ~ f :=
  fun x => (alph x)^-1.
Instance homotopy_symmetric (A : Type) (P : A -> Type)
  : Symmetric (@homotopy A P).
Proof.
  exact homotopy_sym.
Defined.

Example homotopy_tr {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) (alph : f ~ g) (beta : g ~ h) : f ~ h :=
  fun x => (alph x) • (beta x).
Instance homotopy_transitive (A : Type) (P : A -> Type)
  : Transitive (@homotopy A P).
Proof.
  exact homotopy_tr.
Defined.


Lemma homotopy_eucl_l {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) : f ~ g -> f ~ h -> g ~ h.
Proof.
  intros alph beta.
  apply homotopy_sym in alph.
  apply (homotopy_tr g f h alph beta).
Qed.

Lemma homotopy_eucl_r {A : Type} {P : A -> Type}
  (f g h : Π (x : A), P x) : f ~ h -> g ~ h -> f ~ g.
Proof.
  intros alph beta.
  apply homotopy_sym in beta.
  apply (homotopy_tr f h g alph beta).
Qed.


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
  apply ref_unit.
Qed.


Definition logeqv (A B : Type) : Type
  := (A -> B) × (B -> A).
Infix "<->" := logeqv
  : type_scope.

Example logeqv_ref (A : Type) : A <-> A := (id, id).
Instance logeqv_reflexive : Reflexive logeqv.
Proof.
  exact logeqv_ref.
Defined.

Example logeqv_sym (A B : Type) : (A <-> B) -> (B <-> A) :=
  fun e => match e with  (f, g) => (g, f) end.
Instance logeqv_symmetric : Symmetric logeqv.
Proof.
  exact logeqv_sym.
Defined.

Example logeqv_tr (A B C : Type) : (A <-> B) -> (B <-> C) -> (A <-> C) :=
  fun e1 e2 => match e1, e2 with (f, f'), (g, g') => (g ∘ f, f' ∘ g') end.
Instance logeqv_transitive : Transitive logeqv.
Proof.
  exact logeqv_tr.
Defined.


Definition qinv {A B : Type} (f : A -> B) : Type
  := ∑ (g : B -> A), ((g ∘ f ~ id) × (f ∘ g ~ id)).


Definition qinv_to_op {A B : Type} (f : A -> B) : qinv f -> B -> A :=
  fun e => fst e.
Notation "f \'" := (qinv_to_op f _)
  (at level 3)
  : core_scope.


Example qinv_id {A : Type} : qinv (@id A).
Proof.
  unfold qinv.
  exists id. split.
  - reflexivity.
  - reflexivity.
Defined.

Example qinv_qinv {A B : Type} (f : A -> B)
  (e : qinv f) : qinv (fst e).
Proof.
  destruct e as [g [alph beta]].
  unfold qinv. unfold fst.
  exists f. split.
  - exact beta.
  - exact alph.
Defined.

Example qinv_comp {A B C : Type} (f : A -> B) (g : B -> C)
  : qinv f -> qinv g -> qinv (g ∘ f).
Proof.
  intros e1 e2.
  destruct e1 as [f' p1].
  destruct e2 as [g' p2].
  destruct p1 as [alph beta].
  destruct p2 as [gamm delt].
  exists (f' ∘ g').
  split.
  - assert (eta : g' ∘ g ∘ f ~ f).
    {
      rewrite <- id_unit_l.
      apply homotopy_comp_r.
      exact gamm.
    }
    apply homotopy_tr with (g := f'∘ f).
    + rewrite <- comp_assoc.
      apply homotopy_comp_l.
      exact eta.
    + exact alph.
  - assert (eta : g ∘ (f ∘ f') ~ g).
    {
      rewrite <- id_unit_r.
      apply homotopy_comp_l.
      exact beta.
    }
    apply homotopy_tr with (g := g ∘ g').
    + rewrite -> comp_assoc.
      apply homotopy_comp_r.
      exact eta.
    + exact delt.
Defined.


Definition isequiv {A B : Type} (f : A -> B) : Type
  := (∑ (g : B -> A), (g ∘ f ~ id)) × (∑ (g : B -> A), (f ∘ g ~ id)).

Lemma qinv_to_isequiv {A B : Type} (f : A -> B) : qinv f -> isequiv f.
Proof.
  intros e.
  destruct e as [g p].
  destruct p as [alph beta].
  split.
  + refine (g, alph).
  + refine (g, beta).
Defined.

Lemma isequiv_to_qinv {A B : Type} (f : A -> B) : isequiv f ->  qinv f.
Proof.
  intros e.
  destruct e as [p q].
  destruct p as [g alph].
  destruct q as [h beta].
  exists g. split.
  + refine alph.
  + assert (gamm: g ~ h).
    {
      apply homotopy_eucl_l with (g ∘ f ∘ h).
      - rewrite <- id_unit_r.
        rewrite <- comp_assoc.
        apply homotopy_comp_l.
        refine beta.
      - rewrite <- id_unit_l.
        apply homotopy_comp_r.
        refine alph.
    }
    refine (fun x => (ap f (gamm x)) • (beta x)).
Defined.

Lemma qinv_iff_isequiv {A B : Type} (f : A -> B) : qinv f <-> isequiv f.
Proof.
  split.
  - apply qinv_to_isequiv.
  - apply isequiv_to_qinv.
Defined.


Definition homeqv (A B : Type) : Type :=
  ∑ (f : A -> B), isequiv f.
Infix "≃" := homeqv
  : type_scope.


Example homeqv_ref (A : Type) : A ≃ A.
Proof.
  exists id.
  apply qinv_to_isequiv.
  exact qinv_id.
Defined.

Instance homeqv_reflexive
  : Reflexive homeqv.
Proof.
  exact homeqv_ref.
Defined.


Example homeqv_sym (A B : Type) : A ≃ B -> B ≃ A.
Proof.
  intros e.
  destruct e as [f p].
  apply isequiv_to_qinv in p.

  unfold homeqv.
  exists (fst p).
  apply qinv_to_isequiv.

  apply qinv_qinv.
Defined.

Instance homeqv_symmetric
  : Symmetric homeqv.
Proof.
  exact homeqv_sym.
Defined.


Example homeqv_tr (A B C : Type) : A ≃ B -> B ≃ C -> A ≃ C.
Proof.
  intros e1 e2.
  destruct e1 as [f p1].
  apply isequiv_to_qinv in p1.
  destruct e2 as [g p2].
  apply isequiv_to_qinv in p2.

  unfold homeqv.
  exists (g ∘ f).
  apply qinv_to_isequiv.

  apply qinv_comp.
  - exact p1.
  - exact p2.
Defined.

Instance homeqv_transitive
  : Transitive homeqv.
Proof.
  exact homeqv_tr.
Defined.