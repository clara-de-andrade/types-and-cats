(** * Primitive types *)

(** Here we simply introduce the primitive types of our type theory. *)

From TypesAndCats Require Export Settings Notations.

(* begin hide *)
Local Unset Elimination Schemes.
  (* TODO: understand *)
(* end hide *)


(** Dependent map types [forall x : A, P x], as well as as anonymous maps
    [fun x : A => t] are built into Coq, so we don't need to define them.
    Instead, we may simply define map types [A -> B] as a special case of
    [forall x : A, P x], when the value of [P x] is constant and computes
    to [B]. We may idiomatically call [A -> B] an _arrow_ type. *)

Definition arr (A B : Type) : Type := forall _ : A, B.

Notation "A -> B" := (arr A B) : type_scope.


(** Pair types [A * B] are defined using Coq's [Record]s, which are very
    similar to C's `struct`s. We define the type [A * B] as a record of
    two fields, [fst : A] and [snd : B], formed by the constructor [pair].
    More formally, [pair] is a map of type [A -> B -> A * B], while [fst],
    [snd] are maps of types [A * B -> A], [A * B -> B], respectively. We
    say more idiomatically that [pair a b] is an _ordered pair_ of the
    terms [a : A] and [b : B], and that [fst], [snd] are _projections_
    from [A * B] to [A], [B]. We also say that [A * B] is the _product_
    of the types [A], [B] for reasons which will eventually become
    clearer. *)

Record prod (A B : Type) : Type := pair {fst : A; snd : B}.

Arguments prod (A B)%type.
Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.
  (* TODO: explain *)

Notation "A * B" := (prod A B) : type_scope.


(** We may use the standard mathematical notation for ordered types,
    denoting [pair x y] instead by [(a, b)]. Moreover, we consider the
    [*] type operator to be right-associative (that is, [A * B * C] means
    [A * (B * C)] as opposed to [(A * B) * C]), and so, we define this
    notation to be right-associative as well (that is, [(a, b, c)] means
    [(a, (b, c)) as opposed to ((a, b), c)]. We say more idiomatically
    that terms of the form [(x1, ..., xn)] are _n-tuples_, and Coq's
    notation system is capable of defining the notation for n-tuples 
    uniformily in terms of [pair]. *)


Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..) : core_scope.

(** Coq has commands for defining the eliminators of [prod] as an
    induuctive type. Namely, the commands bellow define the terms
    [prod_rect] and [prod_rec], and in particular, [prod_rect], or
    [prod_ind] rather, is the inductor for [prod]. (See HoTT book.) *)

Scheme prod_rect := Induction for prod Sort Type.
Scheme prod_rec := Minimality for prod Sort Type.

Definition prod_ind := prod_rect.
Arguments prod_ind {A B} P _. 


(* begin hide *)
Add Printing Let prod.
#[export] Hint Resolve pair : core.
  (* TODO: understand *)
(* end hide *)


(** Similarly to pair types, dependent pair types [exists x : A, P x] are
    defined in Coq using [Record]s. This time, [exists x : A, P x] is a
    record of two fields, [pr1 : A] and [pr2 : P pr1], formed by the
    constructor [exist]. Formally, if [a : A] and [p : P a], then
    [exist a p] is a term of [exists x : A, P x], and we may say more
    idiomatically that [exist a p] is a _dependent ordered pair_ of [a]
    and [p]. We also say that [pr1], [pr2] are _projections_ of
    [exists x : A, P x], where for any [p : exists x : A, P x], we have
    [pr1 p : A] and [pr2 p : P (pr1 p)]. We also define the notation
    [(x1; ...; xn)] for _dependent n-tuples_ in a similar way we did
    above to non-dependent n-tuples. Finally, we define the eliminators
    for [exists] types. *)

Record Sigma {A : Type} (P : A -> Type) : Type :=
  exist {pr1 : A; pr2 : P pr1}.

Arguments Sigma {A}%type P%map.
Arguments exist {A P} _ _.
Arguments pr1 {A P} _.
Arguments pr2 {A P} _.

Notation "'exists' x .. y , P" :=
  (Sigma (fun x => .. (Sigma (fun y => P)) ..)) : type_scope.

Notation "( x ; .. ; y ; z )" :=
  (exist x .. (exist y z) ..) : fib_scope.


Scheme Sigma_rect := Induction for Sigma Sort Type.
Scheme Sigma_rec := Minimality for Sigma Sort Type.

Definition Sigma_ind := Sigma_rect.
Arguments Sigma_ind {_ _}.


(* begin hide *)
Add Printing Let Sigma.
  (* TODO: understand *)

Register Sigma as core.sigT.type.
Register exist as core.sigT.intro.
Register Sigma_rect as core.sigT.rect.
Register pr1 as core.sigT.proj1.
Register pr2 as core.sigT.proj2.
  (* TODO: understand *)

#[export] Hint Resolve exist : core.
  (* TODO: understand *)
(* end hide *)


(** The remaining types can all be defined with [Inductive] and bear
    little need for explanation. For now, we make only a few remarks about
    these types. In particular, the type [A + B] is more idiomatically
    known as the _sum_ of the types [A], [B] while [Unit] is a _terminal_
    type and [Empty] is an _initial_ type. Again, the motive behind these
    names will eventually become clearer. The maps [inl : A -> A + B] and
    [inr : B -> A + B] are said to be _injections_ of [A + B]. *)

Inductive sum (A B : Type) : Type :=
| inl (a : A) : sum A B
| inr (b : B) : sum A B.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Notation "A + B" := (sum A B)
  ( at level 50,
    left associativity ) : type_scope.


Scheme sum_ind := Induction for sum Sort Type.

Definition sum_rec := sum_ind.
Definition sum_rect := sum_ind.


(** The [Unit] type is defined inductively to have a single constructor,
    [tt : Unit]. As we will later prove, [tt] is the only term of this
    type, and any type having a unique term is (in a suitable sense)
    equivalent to [Unit]. *)

Inductive Unit : Type :=
| tt : Unit.

Scheme Unit_ind := Induction for Unit Sort Type.
Scheme Unit_rec := Minimality for Unit Sort Type.

Definition Unit_rect := Unit_ind.


(* begin hide *)
Register Unit as core.IDProp.type.
Register Unit as core.True.type.
Register tt as core.IDProp.idProp.
Register tt as core.True.I.
  (* TODO: understand *)

#[export] Hint Resolve tt : core.
  (* TODO: understand *)
(* end hide *)


(** The [Empty] type is defined inductively to have no constructors,
    and so, there is no possible way to construct a term of [Empty],
    meaning this type has no terms. *)

Inductive Empty : Type := .

Scheme Empty_ind := Induction for Empty Sort Type.
Scheme Empty_rec := Minimality for Empty Sort Type.

Definition Empty_rect := Empty_ind.


(* begin hide **)
Register Empty as core.False.type.
  (* TODO: understand *)
(* end hide *)


(** We define the following alternative notation for [Unit] and [Empty],
    which follow from interpreting them as terminal and initial types,
    respectively. *)

Notation "1" := Unit : type_scope.
Notation "0" := Empty : type_scope.


(** A (perhaps, unsurprisingly) ubiqutous type is the type [Nat] of
    natural numbers, and its inductive definition should be the most
    familiar one. It has only two constructors, [O : Nat] and
    [S : Nat -> Nat], which respectively denote the _zero_ constant and
    the _successor_ map of [Nat]. *)

Inductive Nat : Type :=
| O : Nat
| S (n : Nat) : Nat.
  (* throws bad-set-minimization *)

Scheme Nat_ind := Induction for Nat Sort Type.
Scheme Nat_rec := Minimality for Nat Sort Type.

Definition Nat_rect := Nat_ind.

(* begin hide *)
(** printing Nat #&#x2115;# *)
  (* for printing [Nat] as ℕ in the docs. *)
Notation "'ℕ'" := Nat.
  (* for printing [Nat] as ℕ in the IDE. *)
(* end hide *)


(** We will use numerals 0, 1, 2, ... and symbols like [+] and [*] in
    various ways. Just above, we used [+], [*] as type formers and [0],
    [1] as types, though we may want to use them instead as symbols for
    addition and multiplication over [Nat], and for the zero and unit of
    [Nat], respectively. Hence, we declare a scope to use these symbols
    in this way, binding it to [Nat]. For instance, we define below the
    notation for using numerals as numbers. *)

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.

Bind Scope nat_scope with Nat.


Arguments S _%nat.

Local Open Scope nat.

Notation "0" := O : nat_scope.
Notation "n + 1" := (S n%nat) : nat_scope.

Notation "1" := 0 + 1 : nat_scope.
Notation "2" := 1 + 1 : nat_scope.
Notation "3" := 2 + 1 : nat_scope.
Notation "4" := 3 + 1 : nat_scope.
Notation "5" := 4 + 1 : nat_scope.

Local Close Scope nat.


(** Last but not least, we inductively define the type [a = b :> A], where
    [a : A] and [b : B] are terms of the same type [A]. We may also denote
    this simply by [a = b] when the type [A] can be inferred from context.
    In particular, for any [a : A], the type [a = a] has a term [refl a],
    where [refl] is a dependent map of type [forall x : A, (x = x)]. *)

Inductive Id {A : Type} : A -> A -> Type :=
| refl (a : A) : Id a a.
Arguments refl {A}%type a.

Notation "a = b :> A" := (@Id A a b) : type_scope.
Notation "a = b" := (a = b :> _) : type_scope.


Scheme Id_ind := Induction for Id Sort Type.
Scheme Id_rec := Minimality for Id Sort Type.

Definition Id_rect := Id_ind.

Arguments Id_ind [A] a P f y p : rename.
Arguments Id_rec [A] a P f y p : rename.


Declare Scope path_scope.
Delimit Scope path_scope with path.
Bind Scope path_scope with Id.


(* begin hide *)
Register Id as core.identity.type.
Register refl as core.identity.refl.
Register Id_rect as core.identity.ind.
  (* TODO: understand *)

#[export] Hint Resolve refl : core.
  (* TODO: understand *)
(* end hide *)


(** There is a famous correspondence between types and their terms, and
    propositions and their proofs, called the _Curry-Howard isomorphism_,
    which allow us to reason type-theoretically about formal proofs. For
    instance, as the notation suggests, an arrow type [A -> B] corresponds
    to an implication from [A] to [B], and a map [f] of this type is a
    proof of this implication in the sense that, for any proof [a : A] of
    the antecedent, this map yields a proof [f a : B] of the consequent.
    Similarly, the type [forall x : A, P x] corresponds to a universal
    proposition, and a map [f] of this type is a proof of that proposition
    in the sense that, for any term [x : A] of the type [A], this map
    yields a proof [f x : P x] of the proposition [P x] depending on
    this variable.

    That all being said, we will formally define what it means for a type
    to be a proposition after we sufficiently develop our type theory, and
    until then, if we speak of types as propositions and terms as proofs,
    we mean it informally, as a simple suggestion for the reader to think
    about the types as expressing conditions about their components and
    the terms as witnesses to the satisfaction of those conditions. For
    instance, the type [a = b :> A], understood in this way, expresses a
    condition of equality between terms [a b : A] of type [A], and in
    particular, for any [a : A], the term [refl a] is a witness to the
    equality [a = a :> A] between [a] and itself, or more tersely, to
    [a] satisfying the condition of "being a term of type [A] equal to
    itself".

    Nevertheless, we may informally interpret types in other ways which
    may be more convenient or instructive. More specifically, when we
    interpret types _topologically_, as (topological) _spaces_, and their
    terms as _points_ in those spaces, then we may alternatively interpret
    the type [a = b :> A] as a space of _paths_ between points [a b : A]
    in [A]. However, the connection between paths and equalities, and the
    underlying correspondence between type theory and topology, runs even
    deeper, and the aim of these notes is to introduce the reader to the
    elementary portion of _homotopy type theory_, or simply HoTT, which
    is a small step away from our formal type theory as we have presented
    it so far. *)

(** TODOs:
    - explain eliminators (induction, recursor)
    - explain pattern matching in terms of them
    - explain scopes
    - understand [Register] and [Hint] commands
    - fix typos, unify typography (commas)
    - write better introduction
    - edit .css/preamble tp pretty-print [Nat] and other tokens
**)