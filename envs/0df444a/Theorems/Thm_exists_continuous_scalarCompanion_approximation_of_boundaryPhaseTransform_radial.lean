-- Prove2me | Theorems.Thm_exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform_radial
-- name    : exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:40.872363+00:00
-- url     : https://prove2.me/theorems/d551b4bd-a9b6-47c5-9c65-5860386e79e4
-- title:
--   exists continuous scalar Companion approximation of boundary Phase Transform radial: exists continuous scalar Companion approximation of boundary Phase Transform radial
-- statement:
--   On a winding-normalized smooth domain, exterior decay and radial geometry
--   automatically supply boundedness and the convergence needed by the canonical
--   phase-controlled scalar companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L29-L77
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L29-L77

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

theorem exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform_radial
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
        1 / ((j : ℝ) + 1))
    (hPlemelj :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∃ (g : ℂ → ℂ) (q : ℕ → Polynomial ℂ),
      ContinuousOn g
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ closure Omega.carrier,
        ‖g z‖ ≤ polynomialSupNorm p (closure Omega.carrier)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
        ‖Polynomial.eval z (q j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A Omega g =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by sorry
