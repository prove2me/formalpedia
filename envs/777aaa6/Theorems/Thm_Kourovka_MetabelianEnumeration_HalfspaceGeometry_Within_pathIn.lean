-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceGeometry_Within_pathIn
-- name    : Kourovka.MetabelianEnumeration.HalfspaceGeometry.Within.pathIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:56.601896+00:00
-- url     : https://prove2.me/theorems/a9af77fb-ce92-47f8-a286-61bffd8ec373
-- title:
--   Within: path In
-- statement:
--   The Within construction uses the path In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L99-L103
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceGeometry.lean#L99-L103

import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceGeometry
variable {X : Type*}

theorem Kourovka.MetabelianEnumeration.HalfspaceGeometry.Within.pathIn {f : X → ℝ} {l u p : ℝ} {xs : List X}
    (h : Within f l u p xs) : PathIn f (fun x => l ≤ x ∧ x ≤ u) p xs := by sorry
