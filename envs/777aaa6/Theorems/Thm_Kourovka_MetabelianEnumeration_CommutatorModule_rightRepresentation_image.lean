-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_rightRepresentation_image
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.rightRepresentation_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:10:29.556264+00:00
-- url     : https://prove2.me/theorems/22d030f9-ddde-47e1-9681-cd22d65a6264
-- title:
--   Commutator Module: right Representation image
-- statement:
--   The Commutator Module construction uses the right Representation image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L117-L119
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L117-L119

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Definitions.Def_Kourovka_Modules_CommutatorModule
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
variable {E Q : Type} [Group E] [CommGroup Q]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]

theorem Kourovka.MetabelianEnumeration.CommutatorModule.rightRepresentation_image (g : E) (a : Additive π.ker) :
    (rightRepresentation π hπ (π g) a).toMul.val = g⁻¹ * a.toMul.val * g := by sorry
