-- Prove2me | Theorems.Thm_exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
-- name    : exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:56.850091+00:00
-- url     : https://prove2.me/theorems/679fb4ae-c120-59f2-ab54-b26a38e87157
-- title:
--   exists continuous scalar Companion approximation of boundary Phase Transform: exists continuous scalar Companion approximation of boundary Phase Transform
-- statement:
--   Regularized Plemelj convergence and the sharp boundary-phase inequality
--   turn the canonical closed scalar companion into the exact continuous and
--   contractive datum used by the polynomial-approximation route.  Approximation
--   and reproduction of its auxiliary contour remain explicit analytic inputs.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionAssembly.lean#L39-L92
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionAssembly.lean#L39-L92

import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]

theorem exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
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
