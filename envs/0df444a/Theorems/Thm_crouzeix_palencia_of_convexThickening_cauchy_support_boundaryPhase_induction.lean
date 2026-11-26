-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:44:22.895102+00:00
-- url     : https://prove2.me/theorems/58448da8-6528-4759-99f7-46c48120852f
-- title:
--   crouzeix palencia of convex Thickening cauchy support boundary Phase induction: crouzeix palencia of convex Thickening cauchy support boundary Phase induction
-- statement:
--   The smooth-thickening scalar-companion route needs only a
--   cancellation-preserving positive-degree induction step for the sharp phase
--   invariant.  Branching divided-difference induction supplies all-polynomial
--   phase contractivity, after which the Plemelj assembly and fourth-power
--   bootstrap give the exact Crouzeix--Palencia conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L195-L248
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L195-L248

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_induction
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
    (hphaseStep : ∀ (n : ℕ) (p : Polynomial ℂ), 0 < p.natDegree →
      (∀ xi ∈ frontier (Omega n).carrier,
        CrouzeixBoundaryPhaseContractive (Omega n)
          (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      CrouzeixBoundaryPhaseContractive (Omega n) p)
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
