-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:34.769272+00:00
-- url     : https://prove2.me/theorems/fab2e5c3-738c-4d52-9c65-c891af24ebac
-- title:
--   Collection: abs unit Sign
-- statement:
--   The Collection construction uses the abs unit Sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L65-L66
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L65-L66

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign (z : ℤ) : |unitSign z| = 1 := by sorry
