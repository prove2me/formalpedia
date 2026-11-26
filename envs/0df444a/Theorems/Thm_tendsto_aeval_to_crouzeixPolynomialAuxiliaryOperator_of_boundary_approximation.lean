-- Prove2me | Theorems.Thm_tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation
-- name    : tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:36:57.082591+00:00
-- url     : https://prove2.me/theorems/b4d4f05b-ed98-4ba4-b043-e76d7564ec90
-- title:
--   tendsto aeval to crouzeix Polynomial Auxiliary Operator of boundary approximation: tendsto aeval to crouzeix Polynomial Auxiliary Operator of boundary approximation
-- statement:
--   Uniform approximation of the conjugate polynomial boundary datum at rate
--   `1 / (j + 1)` implies operator-norm convergence of the polynomial evaluations
--   to the canonical Crouzeix auxiliary operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionConvergence.lean#L132-L152
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionConvergence.lean#L132-L152

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem tendsto_aeval_to_crouzeixPolynomialAuxiliaryOperator_of_boundary_approximation
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (q : ℕ → Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : ∀ j, Polynomial.aeval A (q j) =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
          Omega.boundaryParam)
    (happrox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤
          1 / ((j : ℝ) + 1)) :
    Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
      (nhds (crouzeixPolynomialAuxiliaryOperator A Omega p)) := by sorry
