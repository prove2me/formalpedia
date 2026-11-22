-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_HalfspaceLoops_conjugate_neg
-- name    : Kourovka.MetabelianEnumeration.HalfspaceLoops.conjugate_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:59:51.128172+00:00
-- url     : https://prove2.me/theorems/efddcde3-6b68-4d82-93f3-e55702340cc1
-- title:
--   Halfspace Loops: conjugate neg
-- statement:
--   The Halfspace Loops construction uses the conjugate neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L53-L56
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean#L53-L56

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
variable [IsMulCommutative π.ker]

theorem Kourovka.MetabelianEnumeration.HalfspaceLoops.conjugate_neg (g : E) (n : Additive π.ker) :
    conjugate π g (-n) = -conjugate π g n := by sorry
