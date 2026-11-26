-- Prove2me | Theorems.Thm_tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
-- name    : tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:24.543883+00:00
-- url     : https://prove2.me/theorems/fc92cfdf-fced-4b91-bdbd-bb3ae9fbfd6c
-- title:
--   tendsto aeval to crouzeix Auxiliary Operator of boundary approximation: tendsto aeval to crouzeix Auxiliary Operator of boundary approximation
-- statement:
--   Uniform approximation of a continuous scalar boundary datum at rate
--   `1 / (j + 1)` implies operator-norm convergence of the polynomial evaluations
--   to its normalized resolvent contour integral.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionConvergence.lean#L35-L127
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionConvergence.lean#L35-L127

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (g : ℂ → ℂ)
    (q : ℕ → Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hg : ContinuousOn g
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)))
    (hCauchy : ∀ j, Polynomial.aeval A (q j) =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
          Omega.boundaryParam)
    (happrox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
        g (Omega.boundaryParam t)‖ ≤
          1 / ((j : ℝ) + 1)) :
    Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
      (nhds (crouzeixAuxiliaryOperator A Omega g)) := by sorry
