-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_collection_radius_inverse
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:11.415621+00:00
-- url     : https://prove2.me/theorems/f737c3ab-13d4-459e-9407-a6d92ce7bb02
-- title:
--   Collection: collection radius inverse
-- statement:
--   The second finite-radius statement keeps the literal inverse words,
--   including their reversed block order.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L179-L225
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L179-L225

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius_inverse {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (u v : Lattice k)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k))
    (huv : ‖euclidean (u + v)‖ < ρ) :
    Commute (A p) (conjugate (A q) ((orderedWord t u)⁻¹ * (orderedWord t v)⁻¹)) := by sorry
