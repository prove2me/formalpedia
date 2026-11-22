-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_mul
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.height_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:14.395825+00:00
-- url     : https://prove2.me/theorems/98d96ce5-b0d9-4e21-9d05-7e7795bf615a
-- title:
--   Halfspace Loops: height mul
-- statement:
--   The Halfspace Loops construction uses the height mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L74-L76
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L74-L76

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]
omit [IsMulCommutative ↥π.ker]

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.height_mul (χ : L →+ ℝ) (g h : E) :
    height π χ (g * h) = height π χ g + height π χ h := by sorry
