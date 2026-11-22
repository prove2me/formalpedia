-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_sum_box
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_sum_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:48.294879+00:00
-- url     : https://prove2.me/theorems/d6dc0fef-eaba-4654-852d-019c8070d700
-- title:
--   Collection: abs sum box
-- statement:
--   The Collection construction uses the abs sum box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L129-L131
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionRadius.lean#L129-L131

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_sum_box {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |(latticeAbs u + latticeAbs v) i| = |u i| + |v i| := by sorry
