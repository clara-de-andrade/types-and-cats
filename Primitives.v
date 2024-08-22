(* (adapted from `coq-hott`) *)

From TypesAndCats Require Export Settings.
From TypesAndCats Require Export Notations.


(** TODO: learn and explain *)

Local Unset Elimination Schemes.


(** The inductive type [forall x : A, P x] of _dependent maps_ [fun x => f x]
    from [x : A] to [f x : P x] is built into Coq, so we may not define it.
    Instead, we define the arrow type [arr A B] of (non-dependent) _maps_
    [fun x => f x] from [x : A] to [f x : B], as a special case of the type
    [forall x : A, P x], where [P x] doesn't depended on [x : A] and has a
    constant value of [B], hence [arr A B] is just [forall _ : A, B]. We also
    define the notation [A -> B] for [arr A B], which is more concise. Note
    that [->] is right-associative, so [A -> B -> C] denotes the type
    [A -> (B -> C)] as opposed to the type [(A -> B) -> C], and since [->]
    is not associative in general, those types are distinct from one another.
**)

Definition arr (A B : Type) : Type := forall _ : A, B.
Notation "A -> B" := (arr A B)
  ( at level 99,
    right associativity,
    B at level 200
  ) : type_scope.

(* begin hide *)
(** TODO: learn and explain *)
(*
Definition Compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  map_comp g f.
*)
(* end hide *)

(** We define the inductive type [prod A B], called the _product_ of [A] and
    [B], whose terms [pair a b] are _pairs_ of terms [a : A] and [b : B]. We
    also define the maps [fst : (prod A B) -> A] and [snd : (prod A B) -> B],
    which extract [a] and [b] from the pair [pair a b], respectively. Formally,
    [pair], [fst], [snd] are maps dependent on the types [A], [B] as implicit
    parameters. We also define the eliminators [prod_rect], [prod_rec],
    [prod_ind] for product types.
**)

Record prod (A B : Type) : Type := pair {fst : A; snd : B}.

Arguments prod (A B)%type.
Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Scheme prod_rect := Induction for prod Sort Type.
Scheme prod_rec := Minimality for prod Sort Type.
Definition prod_ind := prod_rect.

Arguments prod_ind {A B} P _. 

(** TODO: learn and explain*)

Add Printing Let prod.
#[export] Hint Resolve pair : core.


(** We define the more idiomatic notation [A * B] for [prod A B], as well
    [A /\ B] for when [A * B] is meant to be interpreted as a conjunction.
    Finally, we define the standard notation for pairs. Note that both [*]
    and [/\] are right-associative, hence, for instance, [A * B * C] denotes
    the type [A * (B * C)]. Similarly, [(x, y, z)] denotes the term
    [(x, (y, z))].
**)

Notation "A * B" := (prod A B)
  ( at level 40,
    right associativity
  ) : type_scope.

Notation "A /\ B" := (prod A B)
  ( at level 80,
    right associativity,
    only parsing
  ) : type_scope.

Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..)
  ( at level 0,
    right associativity
  ) : core_scope.

(** Already we are able to define the type [A <-> B] of _logical equivalences_
    between [A] and [B], which are pairs [(f, g)] of opposite maps [f : A -> B]
    and [g : B -> A]. We are able to define the [uncurry] operation on maps as
    well.
**)

Definition iff (A : Type) (B : Type) : Type := (A -> B) * (B -> A).
Notation "A <-> B" := (iff A B)
  ( at level 95,
    no associativity
  ) : type_scope.

Definition uncurry {A B C : Type} (f : A -> B -> C) (p : A * B) : C :=
  f (fst p) (snd p).
Arguments uncurry {A B C} f%map p. 

(** TODO: learn and explain **)

Local Set Typeclasses Strict Resolution.

(** TODO: learn and explain **)

Definition Relation (A : Type) := A -> A -> Type.
Class Reflexive {A} (R : Relation A) :=
  reflexivity   : forall x,     R x x.
Class Symmetric {A} (R : Relation A) :=
  symmetry      : forall x y,   R x y -> R y x.
Class Transitive {A} (R : Relation A) :=
  transitivity  : forall x y z, R x y -> R y z -> R x z.

Arguments reflexivity {A R _} _.
Arguments symmetry {A R _} _ _ _.
Arguments transitivity {A R _} {_ _ _} _ _.


(** TODO: learn and explain **)

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
(* Tactic Notation "transitivity" constr(x) := etransitivity x. *)


(** For example, we can prove that [->] is a reflexive and transitive relation,
    and so, an instance of the [Reflexive] and [Transitive] typeclasses above.
    Moreover, the proofs of the reflexivity and transitivity of [->] induce the
    _identity_ map [arr_id A : A -> A] on a type [A] and the _composition_
    [arr_comp f g : A -> C] of maps [f : A -> B], [g : B -> C], respectively.
    We also define the more conventional notations [id] and [g o f] for these
    maps.
**)

Global Instance arr_id : Reflexive arr.
Proof.
  intro A.
  intro x.
  exact x.
Defined.
Notation id := (arr_id _%type).

Global Instance arr_comp : Transitive arr.
Proof.
  intros A B C.
  intros f g x.
  exact (g (f x)).
Defined.
Arguments arr_comp {A B C} f g : rename.

Notation "g '∘' f" := (arr_comp f g)
  ( at level 40,
    right associativity
  ) : map_scope.
Notation "g 'o' f" := (g ∘ f)
  ( at level 40,
    right associativity,
    only parsing ) : map_scope.

(** We also define constant maps and composition by dependent maps.
**)

Notation arr_const := (fun x _ => x).
Notation "'const'" := arr_const : map_scope.

Definition arr_compd {A B : Type} {P : B -> Type}
  (f : A -> B) (g : forall x : B, P x)
  : forall x : A, P (f x) := fun x => g (f x).

Global Arguments arr_compd {A B}%type P%map (f g)%map.
#[export] Hint Unfold arr_compd : core.

Notation "g '∘D' f" := (arr_compd f g)
  ( at level 40,
    right associativity
  ) : map_scope.
Notation "g 'oD' f" := (g ∘ f)
  ( at level 40,
    right associativity,
    only parsing ) : map_scope.


(** Moreover, we can prove that [<->] is a reflexive, symmetric and transitive
    relation, and so, an instance of the above typeclasses, which allows for
    using these tactics in proofs involving logical equivalences
**)

Global Instance iff_id : Reflexive iff :=
  fun A => (id, id).

Global Instance iff_inv : Symmetric iff.
Proof.
  intros A B [f g].
  exact (g, f).
Defined.
Arguments iff_inv {A B} p : rename.

Global Instance iff_comp : Transitive iff.
Proof.
  intros A B C [f f'] [g g'].
  exact (g o f, f' o g').
Defined.
Arguments iff_comp {A B C} p q : rename.

(** Next, we define the inductive type [Sigma P], called the _dependent sum_
    of a family [P] over a type [A]. Similarly to [prod], its terms [exist a b]
    are _dependent pairs_ of terms [a : A] and [b : P a], and we may extract them
    with the maps [pr1 : Sigma P -> A], [pr2 : forall p : Sigma P, P (pr1 p)],
    called the _first_ and _second_ projections of [Sigma P], respectively. We
    again define the eliminators [Sigma_rect], [Sigma_rec], [Sigma_ind] for
    dependent sum types. **)

Record Sigma {A : Type} (P : A -> Type) : Type := exist {pr1 : A; pr2 : P pr1}.

Arguments Sigma {A}%type P%map.
Arguments exist {A} P _ _.
Arguments pr1 {A P} _.
Arguments pr2 {A P}%map _.

Scheme Sigma_rect := Induction for Sigma Sort Type.
Scheme Sigma_rec := Minimality for Sigma Sort Type.
Definition Sigma_ind := Sigma_rect.

Arguments Sigma_ind {_ _}.


(** TODO: learn and explain*)

Add Printing Let Sigma.
Register Sigma as core.sigT.type.
Register exist as core.sigT.intro.
Register Sigma_rect as core.sigT.rect.
Register pr1 as core.sigT.proj1.
Register pr2 as core.sigT.proj2.
#[export] Hint Resolve exist : core.


(** We also define more idiomatic notation [exists x : A, P x] for [Sigma P],
    which also fits in the same scheme as [forall x : A, P x]. Moreover, we may
    define a notation for dependent pairs, similarly to non-dependent pairs.
**)

Notation "'exists' x .. y , P" :=
  (Sigma (fun x => .. (Sigma (fun y => P)) ..))
  ( at level 200,
  x binder, y binder,
  right associativity
  ) : type_scope.

Notation "( x ; .. ; y ; z )" := (exist x .. (exist y z) ..)
  ( at level 0,
    right associativity
  ) : fib_scope.

(** Similarly, we define the _sum_ type [sum A B] of [A] and [B], as an
    inductive type, in the usual way. In particular, [sum A B] has as
    constructors the maps [inl : A -> sum A B] and [inr : B -> sum A B], called
    _injections_.
**)

Inductive sum (A B : Type) : Type :=
| inl (a : A) : sum A B
| inr (b : B) : sum A B.

Arguments inl {A B} _ , [A] B _.
  (* ??? *)
Arguments inr {A B} _ , A [B] _.
  (* ??? *)

Scheme sum_ind := Induction for sum Sort Type.
Definition sum_rec := sum_ind.
Definition sum_rect := sum_ind.


(** As with product types, we have a more idiomatic notation [A + B] for
    sum types, as well as [A \/ B] for when [A + B] is meant to be interpreted
    as a disjunction.
**)

Notation "A + B" := (sum A B)
  ( at level 50,
    left associativity ) : type_scope.

Notation "A \/ B" := (A + B)
  ( at level 85,
    right associativity,
    only parsing ) : type_scope.

(** We also define a terminal type [Unit] and an initial type [Empty] as part
    of our standard set of primitive inductive types. Their definitions are
    routine and don't bear much explanation.
**)

Inductive Unit : Type :=
| tt : Unit.

Scheme Unit_ind := Induction for Unit Sort Type.
Scheme Unit_rec := Minimality for Unit Sort Type.
Definition Unit_rect := Unit_ind.

Register Unit as core.IDProp.type.
Register Unit as core.True.type.
Register tt as core.IDProp.idProp.
Register tt as core.True.I.
#[export] Hint Resolve tt : core.
  (* ??? *)


Inductive Empty : Type := .

Scheme Empty_ind := Induction for Empty Sort Type.
Scheme Empty_rec := Minimality for Empty Sort Type.
Definition Empty_rect := Empty_ind.

Register Empty as core.False.type.


(** Note in particular that we can now define the negation [¬ A] of [A] in
    terms of [->] and [Empty], as follows:
**)

Definition not (A : Type) : Type := A -> Empty.
Notation "'¬' A" := (not A)
  ( at level 35,
    right associativity
  ) : type_scope.
Notation "'~' A" := (¬A)
  ( at level 35,
    right associativity,
    only parsing
  ) : type_scope.


(** TODO: document **)

Inductive Nat : Type :=
| O : Nat
| S (n : Nat) : Nat.
Notation "'ℕ'" := Nat.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with Nat.

Arguments S _%nat.

Notation "0" := O : nat_scope.
Notation "1" := (S O) : nat_scope.
Notation "2" := (S (S O)) : nat_scope.
Notation "3" := (S (S (S O))) : nat_scope.
Notation "4" := (S (S (S (S O)))) : nat_scope.
Notation "5" := (S (S (S (S (S O))))) : nat_scope.


(** Finally, we define the inductive type [Id a b] of _paths_ between terms
    [a : A] and [b : A] of the same type. In particular, for any term [a : A],
    the constructor [refl a] gives a path of type [Id a a].
**)

Inductive Id {A : Type} : A -> A -> Type :=
| refl (a : A) : Id a a.

Scheme Id_ind := Induction for Id Sort Type.
Scheme Id_rec := Minimality for Id Sort Type.
Definition Id_rect := Id_ind.

Arguments Id_ind [A] a P f y p : rename.
  (* ??? *)
Arguments Id_rec [A] a P f y p : rename.
  (* ??? *)


(** Proof-theoretically, [Id a b] is the _equality_ type of [a] and [b],
    so we may also denote this type by [a = b :> A], or simply [a = b] if we
    can infer [A] from the context. We also denote the negation of [a = b] by
    [a != b], and call it _unequality_.
**)

Notation "a = b :> A" :=
  (@Id A a b)
  ( at level 70,
    b at next level,
    no associativity
  ) : type_scope.
Notation "a != b :> A" :=
  (not (@Id A a b))
  ( at level 70,
    b at next level,
    no associativity
  ) : type_scope.

Notation "a = b" :=
  (a = b :> _)
  ( at level 70,
    no associativity )
  : type_scope.
Notation "a != b" :=
  (a != b :> _)
  ( at level 70,
    no associativity )
  : type_scope.

(** TODO: learn and explain **)

Register Id as core.identity.type.
Register refl as core.identity.refl.
Register Id_rect as core.identity.ind.


(** TODO: document **)

Bind Scope path_scope with Id.
Local Open Scope path_scope.


Global Instance Id_reflexive {A : Type} : Reflexive (@Id A)
  := refl.
Arguments Id_reflexive / .
  (* ??? *)

Notation "1" := (refl _%path) : path_scope.


Definition inverse {A : Type} {a b : A} (p : a = b) : b = a.
Proof.
  induction p.
  reflexivity.
Defined.

Global Instance Id_symmetric {A : Type} : Symmetric (@Id A)
  := @inverse A.
Register inverse as core.identity.sym.
Arguments inverse {A} {a b} p : simpl nomatch.
  (* ??? *)

Notation "p ^" := (inverse p%path)
  ( at level 1 ) : path_scope.


Definition concat {A : Type} {a b c : A}
  (p : a = b) (q : b = c) : a = c.
Proof.
  induction p, q.
  reflexivity.
Defined.

Global Instance Id_transitive {A : Type} : Transitive (@Id A)
  := @concat A.
Register concat as core.identity.trans.
Arguments concat {A} {a b c} p q : simpl nomatch.
  (* ??? *)


Notation "p '•' q" := (concat p%path q%path)
    ( at level 50,
    left associativity ) : path_scope.
Notation "p '@' q" := (concat p%path q%path)
    ( at level 50,
    left associativity,
    only parsing ) : path_scope.


Definition transport_l {A : Type} {a b : A}  (P : A -> Type) (p : a = b)
  : P a -> P b := match p with refl x => id end.

Arguments transport_l {A}%type {a b} P%map p%path : simpl nomatch.

Notation transport := transport_l.
Notation "p #" := (transport _ p%path)
  ( at level 1,
    left associativity,
    only parsing) : path_scope.

Definition transport_r {A : Type} {a b : A}  (P : A -> Type) (p : a = b)
  : P b -> P a := match p with refl x => arr_id (P x) end.

Arguments transport_r {A}%type {a b} P%map p%path : simpl nomatch.


Definition ap {A B : Type} {a b : A} (f : A -> B) (p : a = b)
  : f a = f b := match p with refl x => refl (f x) end.

Register ap as core.identity.congr.
Global Arguments ap {A B}%type {a b} f%map p%path.


Definition apd {A : Type} {P : A -> Type} {a b : A}
  (f : forall x : A, P x) (p : a = b)
  : p # (f a) = f b := match p with refl x => refl (f x) end. 

Arguments apd {A}%type {P}%map {a b} f%map p%path : simpl nomatch.


#[export] Hint Resolve refl inverse : path_hints.
  (* ??? *)
#[export] Hint Resolve refl : core.
  (* ??? *)


(** TODO(?): scope for homotopies **)


Definition homotopy {A : Type} {P : A -> Type}
  (f g : forall x : A, P x) : Type := forall x : A, f x = g x.

Notation "f == g" :=
  (homotopy f%map g%map)
  ( at level 70,
    no associativity ) : map_scope.


Definition hid {A : Type} {P : A -> Type}
  (f : forall x : A, P x) : f == f := fun x => refl (f x).

Global Instance homotopy_reflexive {A : Type} {P : A -> Type}
  : Reflexive (@homotopy A P) := hid.
Arguments hid {A}%type {P}%map {f}%map : simpl nomatch.


Definition hinv {A : Type} {P : A -> Type} {f g : forall x : A, P x}
  (alph : f == g) : g == f := fun x => (alph x)^.

Global Instance homotopy_symmetric {A : Type} {P : A -> Type}
  : Symmetric (@homotopy A P) := @hinv A P.
Arguments hinv {A}%type {P}%map {f g}%map alph%map : simpl nomatch.


Definition hcomp {A : Type} {P : A -> Type} {f g h : forall x : A, P x}
  (alph : f == g) (beta : g == h) : f == h := fun x => (alph x) @ (beta x).

Global Instance homotopy_transitive {A : Type} {P : A -> Type}
  : Transitive (@homotopy A P) := @hcomp A P.
Arguments hcomp {A}%type {P}%map {f g h}%map (alph beta)%map : simpl nomatch.
