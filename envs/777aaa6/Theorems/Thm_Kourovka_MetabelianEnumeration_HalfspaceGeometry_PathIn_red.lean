-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_red
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.red
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:42.148309+00:00
-- url     : https://prove2.me/theorems/4c68924f-69e0-4dfa-9135-52603e202ce2
-- title:
--   Path In: red
-- statement:
--   The Path In construction uses the red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L81-L86
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L81-L86

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.red {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs ys : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs)
    (hr : FreeGroup.Red xs ys) : PathIn (letterHeight h) P p ys := by sorry
