(* (adapted from `coq-hott`) *)

(* load Ltac plugin *)
Declare ML Module "ltac_plugin".
(* load string number notation plugin *)
Declare ML Module "number_string_notation_plugin".

(* activate tactic language for proofs *)
Global Set Default Proof Mode "Classic".
(* force use of bullets in proofs *)
Global Set Default Goal Selector "!".

(* universe settings *)
Global Set Universe Polymorphism.
Global Unset Strict Universe Declaration.
Global Unset Universe Minimization ToSet.

(* projections settings *)
Global Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.
Global Set Printing Primitive Projection Parameters.

(* pattern matching settings *)
Global Set Asymmetric Patterns.

(* unification settings *)
Global Set Keyed Unification.

(* typeclasses settings *)
Global Set Loose Hint Behavior "Strict".
Create HintDb rewrite discriminated.
#[export] Hint Variables Opaque : rewrite.
Create HintDb typeclass_instances discriminated.

(* search settings *)
Add Search Blacklist "_admitted" "_subproof" "Private_".

(* here be dragons... *)
#[universes(polymorphic=yes)] Definition ReverseCoercionSource (T : Type) := T.
#[universes(polymorphic=yes)] Definition ReverseCoercionTarget (T : Type) := T.
#[warning="-uniform-inheritance", reversible=no, universes(polymorphic=yes)]
Coercion reverse_coercion {T' T} (x' : T') (x : ReverseCoercionSource T)
  : ReverseCoercionTarget T' := x'.
Register reverse_coercion as core.coercion.reverse_coercion.