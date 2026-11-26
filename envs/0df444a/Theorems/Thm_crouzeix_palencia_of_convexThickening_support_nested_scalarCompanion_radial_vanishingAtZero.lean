-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_support_nested_scalarCompanion_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_convexThickening_support_nested_scalarCompanion_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:08.62481+00:00
-- url     : https://prove2.me/theorems/17096e0e-df42-47f7-acb8-5aa0b5edc31e
-- title:
--   crouzeix palencia of convex Thickening support nested scalar Companion radial vanishing At Zero: crouzeix palencia of convex Thickening support nested scalar Companion radial vanishing At Zero
-- statement:
--   The canonical metric-thickening specialization of the strictly nested
--   scalar-companion assembly.  Identifying the smooth carriers with the explicit
--   open thickenings automatically supplies their adjacent closure nesting, while
--   the corresponding closed thickenings supply the compact antitone exhaustion.
--
--   Consequently no separate Plemelj identity, contour-mass identity, winding
--   normalization, or exhaustion data is required.  The remaining analytic input
--   is uniform polynomial approximation of positive-degree closed companions that
--   vanish at zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L919-L985
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L919-L985

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

theorem crouzeix_palencia_of_convexThickening_support_nested_scalarCompanion_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
