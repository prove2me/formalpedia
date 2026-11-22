-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_radius
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:59.135344+00:00
-- url     : https://prove2.me/theorems/591d6afb-689c-433f-b7eb-788069433bb8
-- title:
--   Collection: collection radius
-- statement:
--   The finite-radius collection statement for two ordered words.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L144-L175
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L144-L175

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (u v : Lattice k)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k))
    (huv : ‖euclidean (u + v)‖ < ρ) :
    Commute (A p) (conjugate (A q) (orderedWord t u * orderedWord t v)) := by sorry
