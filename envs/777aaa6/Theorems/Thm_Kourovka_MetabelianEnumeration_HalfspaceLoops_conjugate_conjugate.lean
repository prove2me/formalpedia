-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_conjugate_conjugate
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.conjugate_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:42.948981+00:00
-- url     : https://prove2.me/theorems/b31ce124-68f0-4fb3-9fda-01c4ea37b1c1
-- title:
--   Halfspace Loops: conjugate conjugate
-- statement:
--   The Halfspace Loops construction uses the conjugate conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L59-L65
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L59-L65

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

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.conjugate_conjugate (p x : E) (n : Additive π.ker) :
    conjugate π p (conjugate π x n) = conjugate π (p * x) n := by sorry
