-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_congr_boundaryParam
-- name    : crouzeixAuxiliaryOperator_congr_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:24.952502+00:00
-- url     : https://prove2.me/theorems/028fa880-ef03-5791-914f-db4a99532450
-- title:
--   crouzeix Auxiliary Operator congr boundary Param: crouzeix Auxiliary Operator congr boundary Param
-- statement:
--   Auxiliary contours depend only on the scalar datum along the chosen
--   boundary parametrization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L82-L98
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L82-L98

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

theorem crouzeixAuxiliaryOperator_congr_boundaryParam
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      f (Omega.boundaryParam t) = g (Omega.boundaryParam t)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by sorry
