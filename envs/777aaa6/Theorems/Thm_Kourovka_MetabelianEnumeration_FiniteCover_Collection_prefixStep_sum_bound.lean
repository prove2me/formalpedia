-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefixStep_sum_bound
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.prefixStep_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:01.441443+00:00
-- url     : https://prove2.me/theorems/dc59568e-7a0c-4627-97a6-f03a5e9d8d5b
-- title:
--   Collection: prefix Step sum bound
-- statement:
--   The Collection construction uses the prefix Step sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L120-L147
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L120-L147

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.prefixStep_sum_bound {k : ℕ} (hk : 1 ≤ k) (reverse : Bool) (v : Lattice k) (j : Fin k)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hsmall : ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k) :
    (∑ i, |(prefixStep reverse v j i : ℝ)|) ≤ ((k : ℝ) - 1) * (ρ / k) + 1 := by sorry
