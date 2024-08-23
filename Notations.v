(* (adapted from `coq-hott`) *)

Declare Scope type_scope.
Bind Scope type_scope with Sortclass.

Declare Scope map_scope.
Bind Scope map_scope with Funclass.

(* bug fix *)
Local Set Warnings Append "-skip-spaces-curly".

Notation "'forall'  x .. y , P" :=
  (forall x , .. (forall y, P) ..)
  ( at level 200,
    x binder, y binder,
    right associativity ).

Reserved Notation "'exists' x .. y , p"
  ( at level 200,
  x binder, y binder,
  right associativity,
  format "'[' 'exists' '/ ' x .. y , '/ ' p ']'" ).

Reserved Notation "( x , .. , y , z )"
  ( at level 0,
    right associativity ).

Reserved Notation "x -> y"
  ( at level 99,
    right associativity,
    y at level 200 ).
Reserved Notation "x <-> y"
  ( at level 95,
    no associativity ).

Reserved Notation "'¬' x"
  ( at level 35,
    right associativity ).
Reserved Notation "x /\ y"
  ( at level 80,
    right associativity ).
Reserved Notation "x \/ y"
  ( at level 85,
    right associativity ).

Reserved Notation "x + 1"
  ( at level 1,
    left associativity,
    format "x '+' '/ ' '1'" ).
Reserved Notation "x + y"
  ( at level 50,
    left associativity ).
Reserved Notation "x * y"
  ( at level 40,
    right associativity ).

Reserved Notation "x = y :> T"
  ( at level 70,
    y at next level,
    no associativity ).
Reserved Notation "x != y :> T"
  ( at level 70,
    y at next level,
    no associativity ).

Reserved Notation "x = y"
  ( at level 70,
    no associativity ).
Reserved Notation "x != y"
  ( at level 70,
    no associativity ).

Reserved Notation "x = y = z"
  ( at level 70,
    y at next level,
    no associativity ).

Reserved Notation "x ^"
  ( at level 1,
    left associativity,
    format "x '^'" ).
Reserved Notation "x '@' y"
  ( at level 50,
    left associativity ).
Reserved Notation "x '•' y"
  ( at level 50,
    left associativity ).

Reserved Notation "x == y"
  ( at level 70,
    no associativity ).

Reserved Notation "x ^-1"
  ( at level 1,
    left associativity,
    format "x '^-1'" ).
Reserved Notation "x 'o' y"
  ( at level 50,
    left associativity ).
Reserved Notation "x '∘' y"
  ( at level 50,
    left associativity ).


Declare Scope core_scope.
Declare Scope equiv_scope.
Declare Scope fib_scope.


Delimit Scope type_scope  with type.
Delimit Scope map_scope   with map.

Delimit Scope core_scope  with core.
Delimit Scope equiv_scope with equiv.
Delimit Scope fib_scope   with fib.


Global Open Scope type_scope.
Global Open Scope map_scope.

Global Open Scope core_scope.
Global Open Scope equiv_scope.
Global Open Scope fib_scope.