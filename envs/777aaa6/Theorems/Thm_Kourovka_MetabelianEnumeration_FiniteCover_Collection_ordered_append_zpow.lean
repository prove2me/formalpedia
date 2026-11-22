-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_ordered_append_zpow
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_append_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:48.582056+00:00
-- url     : https://prove2.me/theorems/c4ee3203-7c4c-41d3-9fb2-c8f3aa98fced
-- title:
--   Collection: ordered append zpow
-- statement:
--   Arbitrarily long positive or negative powers can be inserted if the
--   two endpoints remain within the budget.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L114-L135
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L114-L135

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
variable {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
  (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
  (hB : Solid B)
  (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
  (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
include hB ht hs

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_append_zpow (p : Fin a) (v : Lattice k) (i : Fin k) (m : ℤ)
    (hv : v ∈ B) (hm : shift v i m ∈ B) :
    conjugate (A p) (orderedWord t v * t i ^ m) =
      conjugate (A p) (orderedWord t (shift v i m)) := by sorry
