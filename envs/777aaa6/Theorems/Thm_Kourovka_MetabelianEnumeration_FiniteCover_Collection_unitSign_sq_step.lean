-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_unitSign_sq_step
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.unitSign_sq_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:54:51.987163+00:00
-- url     : https://prove2.me/theorems/96ca6673-570c-4967-b095-4bd023239651
-- title:
--   Collection: unit Sign sq step
-- statement:
--   The Collection construction uses the unit Sign sq step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L68-L76
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L68-L76

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.unitSign_sq_step (z : ℤ) :
    ((z - unitSign z : ℤ) : ℝ) ^ 2 = (z : ℝ) ^ 2 - 2 * |(z : ℝ)| + 1 := by sorry
