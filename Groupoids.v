(** * Higher groupoids *)

(** Here we simply develop the fundamental elements of higher category
    theory, and more specifically, the theory of higher groupoids. *)

From TypesAndCats Require Export Primitives.

(** The following code introduces tactics for reflexive, symmetric and
    transitive relations, which will be very useful in what follows. *)

Definition Relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : Relation A) :=
  reflexivity   : forall x,     R x x.
Class Symmetric {A} (R : Relation A) :=
  symmetry      : forall x y,   R x y -> R y x.
Class Transitive {A} (R : Relation A) :=
  transitivity  : forall x y z, R x y -> R y z -> R x z.

Arguments reflexivity {A R _} _ : simpl nomatch.
Arguments symmetry {A R _} _ _ _ : simpl nomatch.
Arguments transitivity {A R _} {_ _ _} _ _ : simpl nomatch.


Tactic Notation "reflexivity" :=
  intros;
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let pre_proof_term_head := constr:(@reflexivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  apply (proof_term_head : forall x, R x x).

Tactic Notation "symmetry" :=
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let x := match goal with |- ?R ?x ?y => constr:(x) end in
  let y := match goal with |- ?R ?x ?y => constr:(y) end in
  let pre_proof_term_head := constr:(@symmetry _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head y x _); change (R y x).

Tactic Notation "transitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _);
  [ change (R x y) | change (R y z) ].
Tactic Notation "transitivity" := transitivity _.

(************************************************************************)

(** ** The higher groupoid structure of paths *)

Local Open Scope path.

(** The [=] types introduce a higher categorial structure on types. More
    concretely, we can view [=] as a binary relation on terms of the same
    type, and prove that it is reflexive, symmetric and transitive. The
    reflexivity follows from the constructor [refl : forall a : A, a = a],
    and the remaining conditions also correspond to terms which we can
    construct by induction, namely the _inverse_ [p^ : b = a] of a path
    [p : a = b] and the _concatenation_ [p @ q] of the paths [p : a = b]
    and [q : b = c]. For good measure, we will also define [1] as notation
    for [refl a] when the term [a] can be inferred from the context. *)

Notation "1" := (refl _%path) : path_scope.

Global Instance Id_reflexive {A : Type} : Reflexive (@Id A)
  := @refl A.
Arguments Id_reflexive / .
  (* throws arguments-assert without the slash. what the heck? *)


Definition path_inverse {A : Type} {a b : A} (p : a = b) : b = a.
Proof.
  induction p.
  reflexivity.
Defined.

Global Instance Id_symmetric {A : Type} : Symmetric (@Id A) :=
  @path_inverse A.
Register path_inverse as core.identity.sym.
Arguments path_inverse {A} {a b} p : simpl nomatch.

Notation "p ^" := (path_inverse p%path) : path_scope.


Definition path_compose {A : Type} {a b c : A}
  (p : a = b) (q : b = c) : a = c.
Proof.
  induction p, q.
  reflexivity.
Defined.

Global Instance Id_transitive {A : Type} : Transitive (@Id A) :=
  @path_compose A.
Register path_compose as core.identity.trans.
Arguments path_compose {A} {a b c} p q : simpl nomatch.

Notation "p '@' q" := (path_compose p%path q%path)
  (only parsing) : path_scope.

(* begin hide *)
Notation "p '•' q" := (path_compose p%path q%path) : path_scope.
  (* for printing [@] as • in the IDE *)
(* end hide *)

(** Moreover, the terms of [=] types, namely paths, themselves satisfy
    various equalities. In particular, [1] is a (left and right) unit,
    and inverses really are (left and right) inverses, with respect to
    concatenation. In addition, concatenation itself is associative,
    and inverses are an involution. All these results are proven below. *)

Lemma concat_p1 {A : Type} {a b : A} (p : a = b)
  : p @ 1 = p.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma concat_1p {A : Type} {a b : A} (p : a = b)
  : 1 @ p = p.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma concat_pV {A : Type} {a b : A} (p : a = b)
  : p @ p^ = 1.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma concat_Vp {A : Type} {a b : A} (p : a = b)
  : p^ @ p = 1.
Proof.
  induction p.
  reflexivity.
Defined. 

Lemma concat_p_pp {A : Type} {a b c d : A}
  (p : a = b) (q : b = c) (r : c = d)
  : p @ (q @ r) = (p @ q) @ r.
Proof.
  induction p, q, r.
  reflexivity.
Defined.

(** Hence, in categorial terms, a type [A] forms a groupoid, where the
    objects are the terms of [A], and the morphims are the paths between
    them. More than this, [A] forms a higher groupoid, since these paths
    themselves have higher paths between them, and the above equalities
    are satisfied by them as well, and so on. *)

(** Moreover, while the types [A], [B] form higher groupoids, therefore the
    maps of type [A -> B] form functors from and to these groupoids. More
    formally, if [f : A -> B] is a map from [A] to [B], then for any path
    [p : a = b] in [A], there exists a path [a p f : f a = f b] in [B],
    and the map [ap f : a = b -> f a = f b] is functorial with respect to
    the groupoid structure of [A] and [B]. *)

Definition ap {A B : Type} (f : A -> B) {a b : A}
  : a = b -> f a = f b.
Proof.
  intros p.
  
  induction p.
  reflexivity.
Defined.
Global Arguments ap {A B}%type f%map {a b} p%path : simpl nomatch.


(* begin hide *)
Register ap as core.identity.congr.
(* end hide*)


Lemma ap_1 {A B : Type} (f : A -> B) {a : A}
  : ap f (refl a) = refl (f a).
Proof.
  reflexivity.
Defined.

Lemma ap_V {A B : Type} (f : A -> B) {a b : A} (p : a = b)
  : ap f (p^) = (ap f p)^.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma ap_pp {A B : Type} (f : A -> B) {a b c : A} (p : a = b) (q : b = c)
  : ap f (p @ q) = (ap f p) @ (ap f q).
Proof.
  induction p, q.
  reflexivity.
Defined.

(** We also have, as is expected, that inverses and concatenations are
    compatible with equality, in the sense that equal paths have equal
    inverses and equal concatenations. We can prove these results
    immediately with the [ap] map, these equalities are proven by terms
    given by [ap] applied to the evident maps. *)

Definition ap_inv {A : Type} {a b : A} (p q : a = b)
  : p = q -> p^ = q^ := ap (fun p => p^).

Definition ap_concat_l {A : Type} {a b c : A} (p p' : a = b) (q : b = c)
  : p = p' -> p @ q = p' @ q := ap (fun p => p @ q).

Definition ap_concat_r {A : Type} {a b c : A} (p : a = b) (q q' : b = c)
  : q = q' -> p @ q = p @ q' := ap (fun q => p @ q).

Lemma ap_concat {A : Type} {a b c : A} (p p' : a = b) (q q' : b = c)
  : p = p' -> q = q' -> p @ q = p' @ q'.
Proof.
  intros h1 h2.
  transitivity.
  - apply (ap_concat_l p p' q).
    apply h1.
  - apply (ap_concat_r p' q q').
    apply h2.
Defined.

(** To prove that the map [refl] is also compatible with equality, we
    want to construct a path [refl a = refl b] given any path [a = b].
    However, [refl a] and [refl b] are of (possibly) distinct types,
    namely [a = a] and [b = b], so we need a way to "transport" the term
    [refl x] from the type [a = a] to the type [b = b], or _vice-versa_.
    Fortunately, we can define a [transport] operation that does that: for
    any type family [P : A -> Type] over a type [A] (where, for instance,
    [P x] is [x = x]), any path [p : a = b] in [A] and any [u : P a]
    (where, for instance, [u] is [refl a]), the [transport_l] operation
    defines a map from [P a] to [P b], where [transport_l P p u : P b].
    There is also a [transport_r] operation which defines an opposite
    map from [P b] to [P a], though we usually refer to [transport_l],
    simply, as [transport], since we only really need one of the two. *)

Definition transport_l {A : Type} {a b : A}  (P : A -> Type) (p : a = b)
  : P a -> P b := match p with refl x => fun u => u end.
Arguments transport_l {A}%type {a b} P%map p%path : simpl nomatch.

Notation transport := transport_l.
Notation "p #" := (transport _ p%path)
  ( at level 1,
    left associativity,
    only parsing) : path_scope.

Definition transport_r {A : Type} {a b : A}  (P : A -> Type) (p : a = b)
  : P b -> P a := match p with refl x => fun u => u end.
Arguments transport_r {A}%type {a b} P%map p%path : simpl nomatch.

(** We then define a dependent generalisation [apd] of the map [ap], which
    applies a dependent map [f : forall x : A, P x] to a path in much the
    same way [ap] applies a non-dependent map to a path. Now we can prove
    that [refl] respects equalities. *)

Definition apd {A : Type} {P : A -> Type} {a b : A}
  (f : forall x : A, P x) (p : a = b)
  : p # (f a) = f b := match p with refl x => refl (f x) end.
Arguments apd {A}%type {P}%map {a b} f%map p%path : simpl nomatch.

Definition apd_refl {A : Type} {a b : A} (p : a = b)
  : p # (refl a) = refl b := apd refl p.

(************************************************************************)

(** ** The [rewrite] tactic *)

(**  *)

(************************************************************************)

(** printing @ #&bull;# *)
  (* for printing [@] as • *)
(** printing o #&#x2218;# *)
  (* for printing [o] as ∘ *)

(** ** Homotopies and a different categorial perspective *)


(** While a map [f : A -> B] corresponds to a functor from and to the
    higher grupoids [A] and [B], in categorial terms, it also corresponds
    with a map between the topological spaces [A] and [B]. In this case,
    the above "functoriality" properties correspond to the preservation of
    paths between these spaces, and so, they imply the continuity of [f].
    On that note, we can type-theoretically define a _homotopy_ between
    maps [f g : A -> B] to be a map of type [forall x : A, f x = g x],
    which is to say, a family of paths between the points mapped by [f]
    and [g]. However, and again categorially, homotopies correspond to
    natural isomorphisms between functors, and in particular, we prove
    that they indeed satisfy the naturality condition. *)

Definition Homotopy {A B : Type} (f g : A -> B) : Type
  := forall x : A, f x = g x.
Notation "f == g" := (Homotopy f%map g%map) : map_scope.

Bind Scope map_scope with Homotopy.

Local Open Scope map.


Lemma concat_ap {A B : Type} {x y : A}
  (f g : A -> B) (alph : f == g) (p : x = y)
  : (alph x) @ (ap g p) = (ap f p) @ (alph y).
Proof.
  induction p.
  transitivity.
  - apply concat_p1.
  - symmetry. apply concat_1p.
Defined.

(** We may note that [==] itself forms a relation that is provably
    reflexive, symmetric and transitive, just like [=]. Indeed, these
    properties of [==] follows from the underlying groupoid structure
    that paths induce on types. *)

Global Instance Homotopy_reflexive {A B : Type}
  : Reflexive (@Homotopy A B) :=
  fun f x => refl (f x).
Global Instance Homotopy_symmetric {A B : Type}
  : Symmetric (@Homotopy A B) :=
  fun _ _ alph x => (alph x)^.
Global Instance Homotopy_transitive {A B : Type}
  : Transitive (@Homotopy A B) :=
  fun _ _ _ alph beta x => (alph x) @ (beta x).

(*

(** TODO: revise, maybe put somewher else *)
(** Moreover, while any type [A] forms a higher groupoid in the sense
    described above, types themselves are the objects of a category whose
    morphisms are the maps between them. To make this structure more
    transparent, we define the _identity_ map [id : A -> A] on a type [A]
    and the _composition_ [g o f : A -> C] of any two maps [f : A -> B],
    [g : B -> C] below. Moreover, [->] itself is a reflexive and transitive
    relation, which is proven by the existence of these terms. *)

Definition arr_id (A : Type) : A -> A :=
  fun x : A => x.
Notation "'id'" := (arr_id _%type) : map_scope.
Global Instance arr_reflexive {A : Type} : Reflexive arr := arr_id.


Definition arr_compose {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun x : A => g (f x).
Notation "g 'o' f" := (arr_compose f%map g%map)
  (only parsing) : map_scope.
Global Instance arr_transitive: Transitive arr := @arr_compose.

(* begin hide *)
Notation "g '∘' f" := (arr_compose f%map g%map) : map_scope.
  (* for printing [o] as ∘ in the IDE *)
(* end hide *)


(** Just as with paths, we have that [id] is a (left and right) unit with
    respect to composition, and that [o] is associative. Moreover, as is
    expected, [==] respects compositions. (TODO: better naming scheme) *)

Lemma arr_id_unit_l {A B : Type} (f : A -> B)
  : id o f == f.
Proof.
  reflexivity.
Defined.

Lemma arr_id_unit_r {A B : Type} (f : A -> B)
  : f o id == f.
Proof.
  reflexivity.
Defined.

Lemma arr_compose_assoc {A B C D : Type}
  (f : A -> B) (g : B -> C) (h : C -> D)
  : h o (g o f) = (h o g) o f.
Proof.
  reflexivity.
Defined.

(* begin hide *)

(** TODO: explain, better naming *)

Definition hom_arr_compose_l' {A B C : Type} (f : A -> B) (g g' : B -> C)
  : g == g' -> g o f == g' o f := fun beta => fun x => beta (f x).

Definition hom_arr_compose_r' {A B C : Type} (f f' : A -> B) (g : B -> C)
  : f == f' -> g o f == g o f' := fun alph => fun x => ap g (alph x).

Lemma hom_arr_compose' {A B C : Type} (f f' : A -> B) (g g' : B -> C)
  : f == f' -> g == g' -> g o f == g' o f'.
Proof.
  intros alph beta.
  transitivity.
  - apply (hom_arr_compose_r' f f' g alph). 
  - apply (hom_arr_compose_l' f' g g' beta).
Defined.
(* end hide *)

(** Hence, types are objects and maps between them are morphisms in a
    certain "ambient" category, namely, the category #&infin;<b>Grpd</b>#
    of higher groupoids, and our formal type theory can be seen as a
    synthetic theory of this category, just as Lawvere's ETCS is a
    synthetic theory of the category #<b>Set</b># of sets. *)

*)


(* ******************************************************************** *)

(** printing Nat #&#x2115;# *)
  (* for printing [Nat] as ℕ *)

(** ** The hierarchy of homotopy types *)

(** As we've seen, with just our primitive types, we can already make some
    very important definitions. In particular, we can define the central
    notion of a type [A] being _contractible_ just in case it has a term
    [x : A] which is equal to that any term [y : A] of this type, meaning
    that there exists a map [contr x : forall y : A, x = y] from any term
    [y : A] to a path [contr x y : x = y] between [x] and [y]. More
    formally: *)

Definition isContr (A : Type) : Type := exists x : A, forall y : A, x = y.

(** We say that any such pair [(x; conrt x)] of type [isContr A] is a
    _centre of contraction_ of the type [A]. Informally, we may also say
    that [x] alone is a centre of contraction of [A] if there exists such
    a map [contr x]. Indeed, for any contractible type [A] and any term
    [x : A], we can define the map [contr x] above given any centre of
    contraction of [A}. *)

Definition contr {A : Type} (c : isContr A) (x : A) : forall y, x = y.
Proof.
  intros y.
  destruct c as [a contr_a].

  transitivity.
  - symmetry. apply contr_a.
  - apply contr_a.
Defined.
    
(** We can immediately prove [Unit] is a contractible type, by constructing
    the map [contr tt : forall x : A, tt = x] by induction. *)

Lemma isContr_Unit : isContr 1.
Proof.
  exists tt.
  induction y.
  reflexivity.
Defined.

(** Moreover, we formally say a type [A] is a _proposition_ just in case
    any two terms of [A] are equal, which is to say, they are connected
    by a path. More formally: *)

Definition isProp (A : Type) : Type := forall (x y : A), x = y.

(** Note that every contractible type is a proposition, because we can
    connect any two terms [x y : A] by a path given in terms of any centre
    of contraction [(a; p_a)]. In particular, [1] is a proposition, with
    [tt] as a centre of contraction, where the map [p_tt] is defined by
    the previous result. [0] is also a proposition, somewhat vacuously. *)

Lemma isContr_to_isProp (A : Type) : isContr A -> isProp A.
Proof.
  intros c.
  intros x y.
  apply (contr c x y).
Defined.

Example isProp_Unit : isProp 1 := isContr_to_isProp 1 isContr_Unit.

Example isProp_Empty : isProp 0.
Proof.
  intros x.
  destruct x.
Defined.

(** Therefore, if [A] is a proposition, we can prove that any term [x : A]
    is a centre of contraction of [A] by constructing the map [p_x] from
    the term inhabiting [isProp A]. More concisely, any proposition is
    "contractible if inhabited." Conversely, every such type is a
    proposition, by the previous result. *)

Lemma isProp_to_contr_if_inhabited (A : Type) : isProp A -> A -> isContr A.
Proof.
  intros f x.
  
  assert (contr_x : forall y : A, x = y)
    by (apply f).
  
  exact (x; contr_x).
Defined.

Lemma contr_if_inhabited_to_isProp (A : Type) : (A -> isContr A) -> isProp A.
Proof.
  intros H x y.

  apply isContr_to_isProp.
  clear y.
  
  apply H.
  exact x.
Defined.

(** In addition, we say that a type [A] is a _set_ just in case any
    equality types [x = y :> A] between its terms [x y : A] is a set.
    This notion of set somewhat diverges from that of axiomatic set
    theories such as ZF(C), and more closely resembles what a type
    theorist would call a _Bishop set_, namely, a type [A] endowed with an
    equivalence relation [R] that forms a proposition [R x y] from any
    terms [x y : A]. *)

Definition isSet (A : Type) : Type := forall x y : A, isProp(x = y).

(** We have that any proposition is also a set, so in particuular [0] and
    [1] are sets. *)

Lemma isProp_to_isSet (A : Type) : isProp A -> isSet A.
Proof.
  intros f x.

  set (g := fun y => f x y).
  assert (lem : forall (y z : A) (p : y = z), p = (g y)^ @ (g z)).
  {
    intros y z p.
    induction p.

    symmetry. apply concat_Vp.
  }

  intros y p q.
  transitivity.
  - apply lem.
  - symmetry. apply lem.
Defined.

Example isSet_Unit : isSet 1 := isProp_to_isSet 1 isProp_Unit.
Example isSet_Empty : isSet 0 := isProp_to_isSet 0 isProp_Empty.

(* begin hide *)
(* TODO: motivate better *)
(** To distinguish propositions and sets in the above sense from those
    in traditional logic and set theory, we may call them _h-propositions_
    and _h-sets_ instead. In particular, they form the types [hSet] and
    [hProp], formally defined below. *)

Definition hProp : Type := exists A : Type, isProp A.
Definition hSet : Type := exists A : Type, isSet A.
(* end hide *)

(** More generally, we may define an infinite cumulative hierarchy of
    _homotopy types_. We say that the _homotopy level_ of a type [A],
    or simply, the _h-level_ of [A], is the least [n : Nat] such that
    [ishType n A] is inhabited, where [htype n A] is defined recursively
    for every [n : Nat] just below. (TODO: introduce [Fixpoint]) We
    also define a type [ishType n] of all types of h-level [n : Nat]. *)

Local Open Scope nat.

Fixpoint ishType (n : Nat) (A : Type) : Type := match n with
  | 0    => isContr A
  | S n' => forall (x y : A), ishType n' (x = y)
  end.

(** To prove that h-levels are cumulative, we must show that, for any
    [n : Nat] and for any type [X], if [X] has h-level [n], then [X] has
    h-level [S n] as well. We prove this result below. *)

Theorem ishType_cumul (n : Nat)
  : forall X : Type, ishType n X -> ishType (S n) X.
Proof.
  induction n as [ | n IHn ].

  - intros X.
    simpl.
    
    intros c.
    destruct c as [a contr_a].

    intros x y.
    unfold isContr.
    exists ((contr_a x)^ @ (contr_a y)).

    intro p.
    induction p.
    apply concat_Vp.

  - intros X H.
    intros x y.

    apply (IHn (x = y)).
    apply H.
Qed.

(* begin hide *)
Definition hType (n : Nat) : Type := exists A : Type, ishType n A.
(* end hide *)

(** In particular, a type is contractible if and only if its h-level is
    0, a proposition if and only if it is 1 (see the proof below), and a
    set if and only if it is 2. On the other hand, groupoids correspond
    precisely with the types of h-level 3, and in general, n-groupoids
    correspond with the types of h-level n + 2, as we will see. Moreover,
    we may informally extend this hierarchy, in order to include all types
    of our theory, by adding an infinite h-level #&infin;# for those types
    which do not attain a finite h-level. In this sense, this type theory
    is a theory of homotopy types, similarly to how the axiomatic set
    theory ZF is a theory of pure sets, namely, the sets which attain a
    transfinite level in the von Neumann hierarchy of sets. *)

Lemma ishType1_to_isProp (A : Type) : ishType 1 A -> isProp A.
Proof.
  simpl.
  intros H x y.
  apply H.
Defined.

Lemma isProp_to_ishType1 (A : Type) : isProp A -> ishType 1 A.
Proof.
  simpl.
  intros f a.
  set (g := f a).
  
  intros y.
  apply isProp_to_contr_if_inhabited.
  - assert (lem : forall (x y : A) (p : x = y), p = (g x)^ @ (g y)).
    {
      induction p as [x].
      symmetry. apply concat_Vp.
    }
    intros p q.
    transitivity.
    + apply lem.
    + symmetry. apply lem.

  - exact (g y).
Qed.


(* ******************************************************************** *)

(** ** Fibers, equivalences and univalence *)

(** So far, we've seen two ways in which to interpret our formal type
    theory: in categorial terms, as a synthetic theory of the category
    #&infin;<b>Grpd</b># of higher grupoids, and alternatively, as a
    theory of homotopy types, in the sense above. However, homotopically,
    homotopy types are actually equivalence classes of topological spaces
    under _homotopic equivalence_, namely, the relation that two spaces
    [A], [B] bear just in case there exist maps [f : A -> B], [g : B -> A]
    such that their compositions [g o f], [f o g] are homotopic to their
    respective identity maps (that is, [g o f == id] and [f o g == id]).
    Though we can state this definition in our theory, our (homotopic)
    types are not necessarily equal just in case they (or rather, their
    underlying spaces) are homotopically equivalent.
    
    We can make this correspondence exact with the _axiom of univalence_,
    also known as _Voevodsky's axiom_, which states that a homotopic
    equivalence between homotopic types, which is itself a homotopic type
    in our theory, is homotopically equivalent to the equality between
    these types. As we will see, this is sufficient to prove that any
    homotopically equivalent homotopy types are indeed equal, as well as
    other useful consequences. That all being said, the above definition
    of (homotopic) equivalence is poorly-behaved in our theory, as we will
    see, so instead we require an alternative, more adequate definition of
    an "equivalence" between homotopy types. To this task, we now turn. *)

(** For any map [f : A -> B] and any [y : B], we denote by [fib f y] the
    _fibre_ of [f] over [y]. Topologically, such a fiber is a subspace of
    [A], but in our theory, [fib f y] is a space whose points [(x; p)]
    consist of a point [x : A] in [A] and a path [p : f x = y] in [B]
    between the points [f x : B] and [y : B]. More formally: *)

Definition fib {A B : Type} (f : A -> B) (y : B)
  : Type := exists x : A, f x = y.

(** We can immediately prove a very useful principle for constructing
    paths between points in a fiber in terms of paths between its
    components. *)

Lemma fib_paths {A B : Type} {f : A -> B} {y : B} (p q : fib f y)
  : (exists gamm : pr1 p = pr1 q, (ap f gamm) @ pr2 q = pr2 p) -> p = q.
Proof.
  induction p as [a u].
  induction q as [b v].
  
  simpl.
  intros [p q'].
  induction p as [x].

  (* assert (q : u = v). *)
Admitted.

  

(* ua <- idtoeqv <- id, isequiv <- fib*)

