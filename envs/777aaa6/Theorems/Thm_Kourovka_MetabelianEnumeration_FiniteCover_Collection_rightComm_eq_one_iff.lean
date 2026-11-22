-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_rightComm_eq_one_iff
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.rightComm_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:27.920916+00:00
-- url     : https://prove2.me/theorems/450579ec-f06d-40c0-90c3-dbf270924190
-- title:
--   Collection: right Comm eq one iff
-- statement:
--   The Collection construction uses the right Comm eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L31-L40
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/Collection.lean#L31-L40

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.rightComm_eq_one_iff (x y : G) : rightComm x y = 1 ↔ Commute x y := by sorry
