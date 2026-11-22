-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_PathIn_toWord_mk
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.toWord_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:54.579188+00:00
-- url     : https://prove2.me/theorems/7540c6ae-600c-45e7-9eb6-7fae813679fe
-- title:
--   Path In: to Word mk
-- statement:
--   The Path In construction uses the to Word mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L88-L92
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L88-L92

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.PathIn.toWord_mk [DecidableEq X] {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs) :
    PathIn (letterHeight h) P p (FreeGroup.mk xs).toWord := by sorry
