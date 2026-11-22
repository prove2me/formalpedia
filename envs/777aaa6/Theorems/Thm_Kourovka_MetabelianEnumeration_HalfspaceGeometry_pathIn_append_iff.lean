-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_pathIn_append_iff
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.pathIn_append_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:59.706495+00:00
-- url     : https://prove2.me/theorems/4d257554-cc43-4473-9d38-69047958fd6b
-- title:
--   Halfspace Geometry: path In append iff
-- statement:
--   The Halfspace Geometry construction uses the path In append iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L47-L63
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L47-L63

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.pathIn_append_iff {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs ys : List X} :
    PathIn f P p (xs ++ ys) ↔
      PathIn f P p xs ∧ PathIn f P (p + (xs.map f).sum) ys := by sorry
