-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceSplitting_not_commute_twist
-- name    : Kourovka.MetabelianEnumeration.HalfspaceSplitting.not_commute_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:31.323372+00:00
-- url     : https://prove2.me/theorems/f1da3ed1-798e-492a-b215-d64e14e74a56
-- title:
--   Halfspace Splitting: not commute twist
-- statement:
--   The Halfspace Splitting construction uses the not commute twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceSplitting.lean#L31-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceSplitting.lean#L31-L46

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]

theorem Kourovka.MetabelianEnumeration.HalfspaceSplitting.not_commute_twist (C : Subgroup N) {a b : N} (ha : a ∉ C) (hb : b ∉ C) :
    ¬ Commute (left C a) (right C b) := by sorry
