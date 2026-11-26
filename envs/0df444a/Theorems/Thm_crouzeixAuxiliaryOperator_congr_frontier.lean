-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_congr_frontier
-- name    : crouzeixAuxiliaryOperator_congr_frontier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:22.556922+00:00
-- url     : https://prove2.me/theorems/8b767732-de63-557f-9aac-5b255fda8320
-- title:
--   crouzeix Auxiliary Operator congr frontier: crouzeix Auxiliary Operator congr frontier
-- statement:
--   In particular, equality on the geometric frontier determines the
--   auxiliary contour.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L103-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L103-L112

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]

theorem crouzeixAuxiliaryOperator_congr_frontier
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : Set.EqOn f g (frontier Omega.carrier)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by sorry
