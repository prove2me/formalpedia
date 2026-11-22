-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:44.322171+00:00
-- url     : https://prove2.me/theorems/e7a0eb0e-ea10-493a-9629-c00f5e92f2f5
-- title:
--   Collection: ordered Word zero
-- statement:
--   The Collection construction uses the ordered Word zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L214-L215
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L214-L215

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero {k : ℕ} (t : Fin k → G) : orderedWord t (0 : Lattice k) = 1 := by sorry
