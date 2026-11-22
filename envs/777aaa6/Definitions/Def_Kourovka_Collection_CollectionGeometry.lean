-- Prove2me | Definitions.Def_Kourovka_Collection_CollectionGeometry
-- name    : Kourovka_Collection_CollectionGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:44:04.888215+00:00
-- url     : https://prove2.me/theorems/7094d89a-5be1-46c0-81d0-79881ac9ae45
-- title:
--   Collection Geometry
-- statement:
--   Definitions and structural lemmas for Collection Geometry, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean

import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
def euclidean {k : ℕ} (v : Lattice k) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))
def latticeAbs {k : ℕ} (v : Lattice k) : Lattice k := fun i => |v i|
def ball {k : ℕ} (ρ : ℝ) : Set (Lattice k) := {v | ‖euclidean v‖ < ρ}
def unitSign (z : ℤ) : ℤ := if 0 < z then 1 else -1
def precedes {k : ℕ} (reverse : Bool) (i j : Fin k) : Prop :=
  if reverse then j < i else i < j
instance {k : ℕ} (reverse : Bool) (i j : Fin k) : Decidable (precedes reverse i j) :=
  inferInstanceAs (Decidable (if reverse then j < i else i < j))
def prefixStep {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) : Lattice k :=
  fun i => if precedes reverse i j then v i else if i = j then unitSign (v j) else 0
def tailStep {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) : Lattice k :=
  v - prefixStep reverse v j
end Kourovka.MetabelianEnumeration.FiniteCover.Collection


