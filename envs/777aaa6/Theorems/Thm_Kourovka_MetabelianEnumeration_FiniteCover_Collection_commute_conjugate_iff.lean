-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_commute_conjugate_iff
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.commute_conjugate_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:17.553877+00:00
-- url     : https://prove2.me/theorems/f4cb7090-6529-4471-b46b-7d4831643742
-- title:
--   Collection: commute conjugate iff
-- statement:
--   The Collection construction uses the commute conjugate iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L239-L245
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionFinite.lean#L239-L245

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.commute_conjugate_iff (a b w : G) :
    Commute a (conjugate b w) ↔ Commute (conjugate a w⁻¹) b := by sorry
