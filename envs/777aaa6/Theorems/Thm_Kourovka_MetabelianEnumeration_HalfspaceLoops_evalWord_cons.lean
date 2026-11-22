-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_evalWord_cons
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:49:23.282162+00:00
-- url     : https://prove2.me/theorems/49c3b024-0790-4456-83ef-5ebd3dfeb9e4
-- title:
--   Halfspace Loops: eval Word cons
-- statement:
--   The Halfspace Loops construction uses the eval Word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L91-L94
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L91-L94

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.evalWord_cons (g : X → E) (z : X × Bool) (w : List (X × Bool)) :
    evalWord g (z :: w) = letter g z * evalWord g w := by sorry
