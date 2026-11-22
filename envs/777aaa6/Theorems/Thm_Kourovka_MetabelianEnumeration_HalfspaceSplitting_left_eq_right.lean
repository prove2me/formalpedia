-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceSplitting_left_eq_right
-- name    : Kourovka.MetabelianEnumeration.HalfspaceSplitting.left_eq_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:30.025056+00:00
-- url     : https://prove2.me/theorems/5c4c04f2-3dc9-423a-95d9-c4cf793edeb1
-- title:
--   Halfspace Splitting: left eq right
-- statement:
--   The Halfspace Splitting construction uses the left eq right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceSplitting.lean#L27-L29
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceSplitting.lean#L27-L29

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]

theorem Kourovka.MetabelianEnumeration.HalfspaceSplitting.left_eq_right (C : Subgroup N) {c : N} (hc : c ∈ C) : left C c = right C c := by sorry
