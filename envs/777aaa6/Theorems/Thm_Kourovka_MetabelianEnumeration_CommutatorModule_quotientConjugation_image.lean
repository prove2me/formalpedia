-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_quotientConjugation_image
-- name    : Kourovka.MetabelianEnumeration.CommutatorModule.quotientConjugation_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:57:43.452174+00:00
-- url     : https://prove2.me/theorems/bf9b30a0-c1e4-46ed-8e71-6a00f8b39b1b
-- title:
--   Commutator Module: quotient Conjugation image
-- statement:
--   The Commutator Module construction uses the quotient Conjugation image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L80-L90
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean#L80-L90

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

theorem Kourovka.MetabelianEnumeration.CommutatorModule.quotientConjugation_image (g : E) :
    quotientConjugation π hπ (π g) = MulAut.conjNormal g := by sorry
