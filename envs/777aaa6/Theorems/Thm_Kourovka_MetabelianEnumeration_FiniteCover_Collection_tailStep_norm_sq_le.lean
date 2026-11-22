-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_tailStep_norm_sq_le
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.tailStep_norm_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:53.224405+00:00
-- url     : https://prove2.me/theorems/2bf17bf4-1c86-428c-8da5-cf5d514f618a
-- title:
--   Collection: tail Step norm sq le
-- statement:
--   The Collection construction uses the tail Step norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L96-L118
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L96-L118

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.tailStep_norm_sq_le {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) :
    ‖euclidean (tailStep reverse v j)‖ ^ 2 ≤ ‖euclidean v‖ ^ 2 - 2 * |(v j : ℝ)| + 1 := by sorry
