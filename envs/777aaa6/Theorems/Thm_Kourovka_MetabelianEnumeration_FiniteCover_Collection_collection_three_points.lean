-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_three_points
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_three_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:41.155001+00:00
-- url     : https://prove2.me/theorems/e9b758bc-3021-4823-9e5b-70ad6caefaff
-- title:
--   Collection: collection three points
-- statement:
--   Collection inside a commutator when both exponent vectors and their
--   sum lie within the budget. The proof moves shrinking coordinates first.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L249-L296
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L249-L296

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_three_points {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (x y : Lattice k) (hx : x ∈ B) (hy : y ∈ B) (hxy : x + y ∈ B) :
    Commute (A p) (conjugate (A q) (orderedWord t x * orderedWord t y)) := by sorry
