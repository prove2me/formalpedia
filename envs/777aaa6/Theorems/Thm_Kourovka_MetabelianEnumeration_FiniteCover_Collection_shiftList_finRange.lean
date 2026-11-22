-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:42.535172+00:00
-- url     : https://prove2.me/theorems/6938f675-646d-4181-8f0d-3a11e811743f
-- title:
--   Collection: shift List fin Range
-- statement:
--   The Collection construction uses the shift List fin Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L159-L161
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L159-L161

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange {k : ℕ} (v w : Lattice k) :
    shiftList v w (List.finRange k) = v + w := by sorry
