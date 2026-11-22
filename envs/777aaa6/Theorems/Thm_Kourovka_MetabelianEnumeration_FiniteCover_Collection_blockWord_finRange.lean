-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:39.929181+00:00
-- url     : https://prove2.me/theorems/3143daf1-d690-43f1-b52b-e99435edbdd1
-- title:
--   Collection: block Word fin Range
-- statement:
--   The Collection construction uses the block Word fin Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L155-L157
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L155-L157

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange {k : ℕ} (t : Fin k → G) (w : Lattice k) :
    blockWord t w (List.finRange k) = orderedWord t w := by sorry
