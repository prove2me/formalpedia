-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.neg_mem_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:45:15.922348+00:00
-- url     : https://prove2.me/theorems/050b5196-e95b-459c-9900-ecde24f40cde
-- title:
--   Collection: neg mem ball
-- statement:
--   The Collection construction uses the neg mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L119-L120
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L119-L120

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.neg_mem_ball {k : ℕ} (v : Lattice k) (ρ : ℝ) :
    -v ∈ ball ρ ↔ v ∈ ball ρ := by sorry
