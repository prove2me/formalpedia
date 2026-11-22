-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_inv
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:00:00.52355+00:00
-- url     : https://prove2.me/theorems/824a849b-913d-42c9-9d74-cbf94c790075
-- title:
--   Halfspace Loops: difference inv
-- statement:
--   The Halfspace Loops construction uses the difference inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L46-L51
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L46-L51

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_inv (u x : E) :
    difference π u x⁻¹ = -conjugate π x⁻¹ (difference π u x) := by sorry
