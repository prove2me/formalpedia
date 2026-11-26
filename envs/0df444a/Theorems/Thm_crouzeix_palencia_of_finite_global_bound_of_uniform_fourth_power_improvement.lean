-- Prove2me | Theorems.Thm_crouzeix_palencia_of_finite_global_bound_of_uniform_fourth_power_improvement
-- name    : crouzeix_palencia_of_finite_global_bound_of_uniform_fourth_power_improvement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:35:34.542711+00:00
-- url     : https://prove2.me/theorems/ed7b70a9-4a27-53b4-98fd-29454925c6d0
-- title:
--   crouzeix palencia of finite global bound of uniform fourth power improvement: crouzeix palencia of finite global bound of uniform fourth power improvement
-- statement:
--   A finite polynomial-calculus bound on the closed numerical range,
--   together with a uniform fourth-power improvement, gives the exact
--   Crouzeix--Palencia conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L493-L511
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L493-L511

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_finite_global_bound_of_uniform_fourth_power_improvement
    (A : E →L[ℂ] E)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A)))
    (hfour : ∀ K : ℝ, 0 ≤ K →
      (∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A))) →
      ∀ p : Polynomial ℂ,
        ‖Polynomial.aeval A p‖ ^ 4 ≤
          (2 * K ^ 3 + K ^ 2) *
            polynomialSupNorm p (closure (numericalRange A)) ^ 4) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
