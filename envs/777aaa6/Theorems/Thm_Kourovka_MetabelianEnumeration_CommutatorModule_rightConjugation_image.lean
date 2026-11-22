-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_rightConjugation_image
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.rightConjugation_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:08.764263+00:00
-- url     : https://prove2.me/theorems/56fd7e80-1e45-4532-be4a-489459f825fa
-- title:
--   Commutator Module: right Conjugation image
-- statement:
--   The Commutator Module construction uses the right Conjugation image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L96-L99
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L96-L99

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

theorem Kourovka.MetabelianEnumeration.CommutatorModule.rightConjugation_image (g : E) (a : π.ker) :
    (rightConjugation π hπ (π g) a).val = g⁻¹ * a.val * g := by sorry
