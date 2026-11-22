-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_tailStep_norm_lt
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.tailStep_norm_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:55:00.956177+00:00
-- url     : https://prove2.me/theorems/09111bc9-0c26-42b6-9639-fdc7ca33d0c5
-- title:
--   Collection: tail Step norm lt
-- statement:
--   The Collection construction uses the tail Step norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L184-L211
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L184-L211

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.tailStep_norm_lt {k : ℕ} (hk : 1 ≤ k) (reverse : Bool) (v : Lattice k)
    (j : Fin k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hlarge : ρ / k ≤ |(v j : ℝ)|)
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k)) :
    ‖euclidean (tailStep reverse v j)‖ < ρ := by sorry
