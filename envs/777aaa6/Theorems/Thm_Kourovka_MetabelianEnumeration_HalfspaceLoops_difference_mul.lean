-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_difference_mul
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:43.129496+00:00
-- url     : https://prove2.me/theorems/2518198a-dfce-442a-b4bb-45a0cef45427
-- title:
--   Halfspace Loops: difference mul
-- statement:
--   The Halfspace Loops construction uses the difference mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L38-L43
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L38-L43

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.difference_mul (u p x : E) :
    difference π u (p * x) = difference π u p + conjugate π p (difference π u x) := by sorry
