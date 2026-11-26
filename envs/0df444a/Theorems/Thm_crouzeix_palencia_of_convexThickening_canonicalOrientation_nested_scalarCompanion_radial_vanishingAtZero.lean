-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_convexThickening_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:14:43.675259+00:00
-- url     : https://prove2.me/theorems/0408f6d4-1016-53ae-911a-2977ce58e7d9
-- title:
--   crouzeix palencia of convex Thickening canonical Orientation nested scalar Companion radial vanishing At Zero: crouzeix palencia of convex Thickening canonical Orientation nested scalar Companion radi
-- statement:
--   The canonical-orientation specialization removes the final geometric
--   support premise from the metric-thickening capstone.  Any supplied smooth
--   realization is reoriented automatically; uniform approximation is required
--   only for the resulting canonically oriented closed scalar companions.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1032-L1054
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1032-L1054

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_convexThickening_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n).canonicalOrientation p z‖ ≤
            1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
