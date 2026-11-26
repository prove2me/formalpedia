-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:01.146151+00:00
-- url     : https://prove2.me/theorems/6fccc78b-ed93-517f-b12b-3384f713fea8
-- title:
--   crouzeix palencia of convex Thickening cauchy support boundary Phase approximation: crouzeix palencia of convex Thickening cauchy support boundary Phase approximation
-- statement:
--   On the explicit smooth thickening exhaustion, the boundary-phase
--   contraction, regularized convergence, polynomial approximation, and contour
--   reproduction together imply the exact Crouzeix--Palencia spectral-set bound.
--
--   This is the direct capstone connector for the scalar-companion route.  The
--   geometric Cauchy and support hypotheses provide the symmetrized estimate and
--   the finite stagewise calculus bound; the canonical scalar companions provide
--   the cancellation-preserving fourth-power input.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionAssembly.lean#L102-L193
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionAssembly.lean#L102-L193

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

theorem crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hreg : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized (Omega n) p xi)
        (nhdsWithin xi (Omega n).carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized
            (Omega n) p xi xi)))
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
