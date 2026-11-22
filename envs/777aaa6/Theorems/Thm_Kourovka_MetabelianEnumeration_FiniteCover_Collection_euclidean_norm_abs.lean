-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
-- name    : Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:40.890079+00:00
-- url     : https://prove2.me/theorems/ccb727a9-8d86-4e66-9de9-e023dbc20afb
-- title:
--   Collection: euclidean norm abs
-- statement:
--   The Collection construction uses the euclidean norm abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L43-L47
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Collection/CollectionGeometry.lean#L43-L47

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection

theorem Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs {k : ℕ} (v : Lattice k) :
    ‖euclidean (latticeAbs v)‖ = ‖euclidean v‖ := by sorry
