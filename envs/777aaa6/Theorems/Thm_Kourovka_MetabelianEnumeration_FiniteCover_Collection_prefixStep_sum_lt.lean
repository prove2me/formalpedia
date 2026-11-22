-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefixStep_sum_lt
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.prefixStep_sum_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:57.365996+00:00
-- url     : https://prove2.me/theorems/e3f63536-5d3b-460e-8119-d227796f0105
-- title:
--   Collection: prefix Step sum lt
-- statement:
--   The Collection construction uses the prefix Step sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L213-L226
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L213-L226

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.prefixStep_sum_lt {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (v : Lattice k) (j : Fin k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hsmall : ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k) :
    (∑ i, |(prefixStep reverse v j i : ℝ)|) < ρ - ρ / (2 * k) := by sorry
