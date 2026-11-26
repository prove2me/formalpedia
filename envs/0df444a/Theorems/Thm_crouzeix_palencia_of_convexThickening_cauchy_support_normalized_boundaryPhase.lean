-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase
-- name    : crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:44:21.600234+00:00
-- url     : https://prove2.me/theorems/3683a9e7-cd0b-588c-80bb-6760234e14ad
-- title:
--   crouzeix palencia of convex Thickening cauchy support normalized boundary Phase: crouzeix palencia of convex Thickening cauchy support normalized boundary Phase
-- statement:
--   Equivalently, the smooth-thickening scalar-companion route only needs the
--   sharp phase theorem for positive-degree polynomials normalized to frontier
--   sup norm one at each stage.  Infinite-frontier normalization supplies all
--   other scales and the constant case.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L254-L306
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L254-L306

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_convexThickening_cauchy_support_normalized_boundaryPhase
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
    (hphaseNormalized : ∀ (n : ℕ) (p : Polynomial ℂ),
      0 < p.natDegree →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
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
