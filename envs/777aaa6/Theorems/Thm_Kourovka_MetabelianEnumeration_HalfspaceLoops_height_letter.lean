-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_letter
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.height_letter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:36.466508+00:00
-- url     : https://prove2.me/theorems/b47000e6-0cb7-46c8-b3c6-4b9f4fb2d630
-- title:
--   Halfspace Loops: height letter
-- statement:
--   The Halfspace Loops construction uses the height letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L97-L100
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L97-L100

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.height_letter (χ : L →+ ℝ) (g : X → E) (z : X × Bool) :
    height π χ (letter g z) = letterHeight (fun x => height π χ (g x)) z := by sorry
