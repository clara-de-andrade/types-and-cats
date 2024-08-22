(* (adapted from `coq-hott`) *)

From TypesAndCats Require Export Settings.
From TypesAndCats Require Export Notations.
From TypesAndCats Require Export Primitives.

Local Open Scope path_scope.


Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p.
Proof.
  induction p.
  reflexivity.
Defined.

Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p.
Proof.
  induction p.
  reflexivity.
Defined.

Definition concat_p1_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p @ 1.
Proof.
  refine (_ @ _^).
  - apply concat_1p.
  - apply concat_p1.
Defined.

Definition concat_1p_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = 1 @ p.
Proof.
  refine (_ @ _^).
  - apply concat_p1.
  - apply concat_1p.
Defined.


Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1.
Proof.
  induction p.
  reflexivity.
Defined.

Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^ @ p = 1.
Proof.
  induction p.
  reflexivity.
Defined.


Definition concat_p_pp {A : Type} {x y z w : A}
  (p : x = y) (q : y = z) (r : z = w) :
  p @ (q @ r) = (p @ q) @ r.
Proof.
  induction p, q, r.
  reflexivity.
Defined.

Definition concat_pp_p {A : Type} {x y z w : A}
  (p : x = y) (q : y = z) (r : z = w) :
  (p @ q) @ r = p @ (q @ r).
Proof.
  induction p, q, r.
  reflexivity.
Defined.


Definition concat_V_pp {A : Type} {x y z : A}
  (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q.
Proof.
  induction p, q.
  reflexivity.
Defined.

Definition concat_p_Vp {A : Type} {x y z : A}
  (p : x = y) (q : x = z) :
  p @ (p^ @ q) = q.
Proof.
  induction p, q.
  reflexivity.
Defined.

Definition concat_pp_V {A : Type} {x y z : A}
  (p : x = y) (q : y = z) :
  (p @ q) @ q^ = p.
Proof.
  induction p, q.
  reflexivity.
Defined.

Definition concat_pV_p {A : Type} {x y z : A}
  (p : x = z) (q : y = z) :
  (p @ q^) @ q = p.
Proof.
  induction p, q.
  reflexivity.
Defined.


Definition inv_V {A : Type} {x y : A} (p : x = y) :
  p^ ^ = p.
Proof.
  induction p.
  reflexivity.
Defined.

Definition inv_pp {A : Type} {x y z : A}
  (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^.
Proof.
  induction p, q.
  reflexivity.
Defined.

Definition inv_Vp {A : Type} {x y z : A}
  (p : x = y) (q : x = z) :
  (p^ @ q)^ = q^ @ p.
Proof.
  induction p, q.
  reflexivity.
Defined.

Definition inv_pV {A : Type} {x y z : A}
  (p : x = z) (q : y = z) :
  (p @ q^)^ = q @ p^.
Proof.
  induction p, q.
  reflexivity.
Defined.

Definition inv_VV {A : Type} {x y z : A}
  (p : y = x) (q : z = y) :
  (p^ @ q^)^ = q @ p.
Proof.
  induction p, q.
  reflexivity.
Defined.


Definition moveR_Mp {A : Type} {x y z : A}
  (p : x = z) (q : y = x) (r : y = z) :
  p = q^ @ r -> q @ p = r.
Proof.
  induction q. intro h.
  refine (_ @ h @ _).
  - apply concat_1p.
  - apply concat_1p.
Defined.

Definition moveL_Mp {A : Type} {x y z : A}
  (p : x = z) (q : x = y) (r : y = z) :
  q^ @ p = r -> p = q @ r.
Proof.
  induction q. intro h.
  refine (_^ @ h @ _^).
  - apply concat_1p.
  - apply concat_1p.
Defined.

Definition moveR_pM {A : Type} {x y z : A}
  (p : x = y) (q : y = z) (r : x = z) :
  p = r @ q^ -> p @ q = r.
Proof.
  induction q. intro h.
  refine (_ @ h @ _).
  - apply concat_p1.
  - apply concat_p1.
Defined.

Definition moveL_pM {A : Type} {x y z : A}
  (p : x = z) (q : x = y) (r : y = z) :
  p @ r^ = q -> p = q @ r.
Proof.
  induction r. intro h.
  refine (_^ @ h @ _^).
  - apply concat_p1.
  - apply concat_p1.
Defined.


Definition moveR_Vp {A : Type} {x y z : A}
  (p : x = z) (q : x = y) (r : y = z) :
  p = q @ r -> q^ @ p = r.
Proof.
  induction q. intro h.
  refine (_ @ h @ _).
  - apply concat_1p.
  - apply concat_1p.
Defined.

Definition moveL_Vp {A : Type} {x y z : A}
  (p : x = y) (q : y = z) (r : x = z) :
  p @ q = r -> q = p^ @ r.
Proof.
  induction p. intro h.
  refine (_^ @ h @ _^).
  - apply concat_1p.
  - apply concat_1p.
Defined.

Definition moveR_pV {A : Type} {x y z : A}
  (p : x = z) (q : x = y) (r : y = z) :
  p = q @ r -> p @ r^ = q.
Proof.
  induction r. intro h.
  refine (_ @ h @ _).
  - apply concat_p1.
  - apply concat_p1.
Defined.

Definition moveL_pV {A : Type} {x y z : A}
  (p : x = y) (q : y = z) (r : x = z) :
  p @ q = r -> p = r @ q^.
Proof.
  induction q. intro h.
  refine (_^ @ h @ _^).
  - apply concat_p1.
  - apply concat_p1.
Defined.


Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  induction p. intro h.
  refine (h @ _).
  apply concat_1p.
Defined.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
  induction q. intro h.
  refine (_^ @ h).
  apply concat_1p.
Defined.

Definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q @ p^ -> p = q.
Proof.
  induction p. intro h.
  refine (h @ _).
  apply concat_p1.
Defined.

Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1 -> p = q.
Proof.
  induction q. intro h.
  refine (_^ @ h).
  apply concat_p1.
Defined.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p @ q -> p^ = q.
Proof.
  induction p. intro h.
  refine (h @ _).
  apply concat_1p.
Defined.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
  induction q. intro h.
  refine (_^ @ h).
  apply concat_1p.
Defined.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q @ p -> p^ = q.
Proof.
  induction p. intro h.
  refine (h @ _).
  apply concat_p1.
Defined.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^.
Proof.
  induction q. intro h.
  refine (_^ @ h).
  apply concat_p1.
Defined.

(*
Definition moveR_V1
Definition moveL_V1
Definition moveR_1V
Definition moveL_1V

Definition moveR_transport_p
Definition moveL_transport_p
Definition moveR_transport_V
Definition moveL_transport_V
Definition moveR_transport_p_V
Definition moveL_transport_p_V
Definition moveR_transport_V_V
Definition moveL_transport_V_V
*)