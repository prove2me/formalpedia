-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_pointOriented_nested_scalarCompanion_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_convexThickening_pointOriented_nested_scalarCompanion_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:46.381737+00:00
-- url     : https://prove2.me/theorems/b20c65d5-9f60-59f0-8395-651c44f1842a
-- title:
--   crouzeix palencia of convex Thickening point Oriented nested scalar Companion radial vanishing At Zero: crouzeix palencia of convex Thickening point Oriented nested scalar Companion radial vanishing A
-- statement:
--   A one-point orientation specialization of the canonical thickening
--   capstone.  At each stage it is enough to exhibit one point of the smooth
--   carrier whose canonical normal has the supporting sign at parameter zero.
--   Strict convexity and continuity propagate that single sign to the whole trace
--   and then to every point of the numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L992-L1026
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L992-L1026

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

theorem crouzeix_palencia_of_convexThickening_pointOriented_nested_scalarCompanion_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (horientation : ∀ n, ∃ c ∈ (Omega n).carrier,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam 0) *
        (c - (Omega n).boundaryParam 0)).re ≤ 0)
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
