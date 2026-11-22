-- Prove2me | Definitions.Def_Kourovka_Collection_CollectionFinite
-- name    : Kourovka_Collection_CollectionFinite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:56.526833+00:00
-- url     : https://prove2.me/theorems/d3f36823-ab79-46e2-bf92-1e519d131fa3
-- title:
--   Collection Finite
-- statement:
--   Definitions and structural lemmas for Collection Finite, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean

import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
def shift {k : ℕ} (v : Lattice k) (i : Fin k) (m : ℤ) : Lattice k :=
  Function.update v i (v i + m)
section Blocks
variable {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
  (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
  (hB : Solid B)
  (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
  (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
include hB ht hs
end Blocks
def blockWord {k : ℕ} (t : Fin k → G) (w : Lattice k) (l : List (Fin k)) : G :=
  (l.map fun i => t i ^ w i).prod
def shiftList {k : ℕ} (v w : Lattice k) (l : List (Fin k)) : Lattice k :=
  fun i => v i + if i ∈ l then w i else 0
end Kourovka.MetabelianEnumeration.FiniteCover.Collection


