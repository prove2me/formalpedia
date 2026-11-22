-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_height_inv
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.height_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:36.36974+00:00
-- url     : https://prove2.me/theorems/7ee2bd02-2f7e-43f1-b03c-5c5ef5cd3b77
-- title:
--   Halfspace Loops: height inv
-- statement:
--   The Halfspace Loops construction uses the height inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L79-L81
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L79-L81

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.height_inv (χ : L →+ ℝ) (g : E) :
    height π χ g⁻¹ = -height π χ g := by sorry
