-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_small_mem_ball
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.small_mem_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:51.087666+00:00
-- url     : https://prove2.me/theorems/5dd677b6-421c-454b-8eb7-efa1922a255d
-- title:
--   Collection: small mem ball
-- statement:
--   The Collection construction uses the small mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L122-L127
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L122-L127

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.small_mem_ball {k : ℕ} (hk : 1 ≤ k) (u : Lattice k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ) (hu : ‖euclidean u‖ ≤ ρ / (2 * k)) : u ∈ ball ρ := by sorry
