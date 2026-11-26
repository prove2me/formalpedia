-- Prove2me | Theorems.Thm_ofReal_crouzeixBoundaryDoubleLayerDensity
-- name    : ofReal_crouzeixBoundaryDoubleLayerDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:52.542409+00:00
-- url     : https://prove2.me/theorems/d3f15a8b-3f0b-5e40-b888-918ea76a0135
-- title:
--   of Real crouzeix Boundary Double Layer Density: of Real crouzeix Boundary Double Layer Density
-- statement:
--   The real density is the difference of the two conjugate Cauchy kernels
--   with the standard `1 / (2 pi i)` normalization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L93-L109
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L93-L109

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem ofReal_crouzeixBoundaryDoubleLayerDensity
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ) :
    (crouzeixBoundaryDoubleLayerDensity Omega xi t : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹ -
          star (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹)) := by sorry
