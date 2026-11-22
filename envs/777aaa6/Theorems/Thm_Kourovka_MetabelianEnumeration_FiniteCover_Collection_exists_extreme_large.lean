-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_exists_extreme_large
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.exists_extreme_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:56.882793+00:00
-- url     : https://prove2.me/theorems/7cb37cf1-f298-4d57-8552-a9e628abc05d
-- title:
--   Collection: exists extreme large
-- statement:
--   The Collection construction uses the exists extreme large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L149-L182
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L149-L182

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.exists_extreme_large {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (v : Lattice k) (ρ : ℝ) (hv : ρ ≤ ‖euclidean v‖) :
    ∃ j : Fin k, ρ / k ≤ |(v j : ℝ)| ∧
      ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k := by sorry
