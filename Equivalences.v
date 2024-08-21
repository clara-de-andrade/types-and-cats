From HoTT Require Import Basics.
From TypesAndCats Require Import Primitives Types Paths.


(** TODO: document *)

Definition homotopy {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) : Type
  := Π (x : A), (f x ~> g x).
Infix "~" := homotopy
  (at level 99)
  : core_scope.


Definition homotopy_ref {A : Type} {P : A -> Type}
  (f : Π (x : A), P x) : f ~ f :=
  fun x => ref (f x).

Instance homotopy_reflexive (A : Type) (P : A -> Type)
  : Reflexive (@homotopy A P).
Proof.
  exact homotopy_ref.
Defined.

Definition homotopy_sym {A : Type} {P : A -> Type}
  (f g : Π (x : A), P x) (alph : f ~ g) : g ~ f :=
  fun x => (alph x)^-1.

Instance homotopy_symmetric (A : Type) (P : A -> Type)
  : Symmetric (@homotopy A P).
Proof.
  exact homotopy_sym.
Defined.

Definition homotopy_tr {A : Type} {P : A -> Type}
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

Definition homotopy_comp_l {A B C : Type}
  (f f' : A -> B) (g : B -> C)
  (alph : f ~ f') : g ∘ f ~ g ∘ f' :=
  homotopy_comp f f' g g alph (homotopy_ref g).

Definition homotopy_comp_r {A B C : Type}
  (f : A -> B) (g g' : B -> C)
  (beta : g ~ g') : g ∘ f ~ g' ∘ f :=
  homotopy_comp f f g g' (homotopy_ref f) beta.


(* TODO: unfold proof *)
Theorem homotopy_naturality {A B : Type}
  (f g : A -> B) (alph : f ~ g)
  {a b : A} (p : a ~> b)
  : (alph a) • (ap g p) ~> (ap f p) • (alph b).
Proof.
  induction p. unfold ap.
  apply eucl_l with (alph a).
  - apply ref_unit_r.
  - apply ref_unit_l.
Qed.


Definition leqv (A B : Type) : Type
  := (A -> B) × (B -> A).
Infix "<->" := leqv
  : type_scope.


Example leqv_ref (A : Type) : A <-> A := (id, id).

Instance leqv_reflexive : Reflexive leqv.
Proof.
  exact leqv_ref.
Defined.


Example leqv_sym (A B : Type) : (A <-> B) -> (B <-> A) :=
  fun e => match e with  (f, g) => (g, f) end.

Instance leqv_symmetric : Symmetric leqv.
Proof.
  exact leqv_sym.
Defined.


Example leqv_tr (A B C : Type) : (A <-> B) -> (B <-> C) -> (A <-> C) :=
  fun e1 e2 => match e1, e2 with (f, f'), (g, g') => (g ∘ f, f' ∘ g') end.
  
Instance leqv_transitive : Transitive leqv.
Proof.
  exact leqv_tr.
Defined.
  

(* TODO: do something with this
Definition qinv {A B : Type} (f : A -> B) : Type
  := ∑ (g : B -> A), ((g ∘ f ~ id) × (f ∘ g ~ id)).

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

Lemma qinv_qinv_id {A : Type}
  : @qinv_qinv A A id qinv_id = qinv_id.
Proof.
  simpl. reflexivity.
Qed.

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


Lemma qinv_qinv_comp {A B C : Type} (f : A -> B) (g : B -> C)
  (e1 : qinv f) (e2 : qinv g)
  : qinv_qinv (g ∘ f) (qinv_comp f g e1 e2)
  = (qinv_comp (fst e2) (fst e1) (qinv_qinv g e2) (qinv_qinv f e1)). 


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

Declare Scope heqv_scope.
Open Scope heqv_scope.

Definition heqv (A B : Type) : Type :=
  ∑ (f : A -> B), isequiv f.
Infix "≃" := heqv
  : type_scope.

Definition heqv_fun {A B : Type} (f : A ≃ B) := (fst f).
Notation "f *" := (heqv_fun f)
  (at level 3)
  : heqv_scope.


Example heqv_ref (A : Type) : A ≃ A.
Proof.
  exists id.
  apply qinv_to_isequiv.
  refine (id, (ref, ref)).
Defined.

Notation "'id'" := (heqv_ref)
  : heqv_scope.

Instance heqv_reflexive
  : Reflexive heqv.
Proof.
  exact heqv_ref.
Defined.


Example heqv_sym (A B : Type) : A ≃ B -> B ≃ A.
Proof.
  intros e.
  destruct e as [f p].
  apply isequiv_to_qinv in p.

  unfold heqv.
  exists (fst p).
  apply qinv_to_isequiv.

  apply qinv_qinv.
Defined.

Notation "f ^-1" := (heqv_sym _ _ f)
  (at level 3)
  : heqv_scope.

Instance heqv_symmetric
  : Symmetric heqv.
Proof.
  exact heqv_sym.
Defined.


Example heqv_tr (A B C : Type) : A ≃ B -> B ≃ C -> A ≃ C.
Proof.
  intros f g.
  destruct f as [f p1].
  destruct g as [g p2].

  unfold heqv.
  exists (g ∘ f).
  apply qinv_to_isequiv.

  apply qinv_comp.
  - apply isequiv_to_qinv.
    exact p1.
  - apply isequiv_to_qinv.
    exact p2.
Defined.

Notation "g ∘ f" := (heqv_tr _ _ _ f g)
  : heqv_scope.

Instance heqv_transitive
  : Transitive heqv.
Proof.
  exact heqv_tr.
Defined.


Definition idtoeqv {A B : Type} : A ~> B -> A ≃ B.
Proof.
  intro p.
  induction p as [X].
  reflexivity.
Defined.

Example idtoeqv_ref {A : Type}
  : idtoeqv (ref A) = heqv_ref A.
Proof.
  simpl.
  reflexivity.
Qed.

Example idtoeqv_sym {A B : Type} (p : A ~> B)
  : idtoeqv (p^-1) ~> heqv_sym _ _ (idtoeqv p).
Proof.
  induction p as [X].
  rewrite -> sym_ref.
  rewrite -> idtoeqv_ref.
  
  assert (Lm : heqv_sym X X (heqv_ref X) = heqv_ref X).
Qed.


Theorem ax_univalence {A B : Type} : isequiv (@idtoeqv A B).
Proof. Admitted.

Corollary Id_heqv_heqv {A B : Type} : (A ~> B) ≃ (A ≃ B).
Proof.
  exists idtoeqv.
  apply ax_univalence.
Qed.


Open Scope heqv_scope.
Definition ua {A B : Type} : (A ≃ B) ≃ (A ~> B) :=
  Id_heqv_heqv^-1.

*)