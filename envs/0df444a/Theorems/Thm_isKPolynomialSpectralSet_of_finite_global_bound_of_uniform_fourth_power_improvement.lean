-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
-- name    : isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:57.892807+00:00
-- url     : https://prove2.me/theorems/237eb88c-ae90-4bbd-a35a-f64b4456bfab
-- title:
--   is KPolynomial Spectral Set of finite global bound of uniform fourth power improvement: is KPolynomial Spectral Set of finite global bound of uniform fourth power improvement
-- statement:
--   On any control set containing the spectrum, a finite polynomial-calculus
--   bound together with a uniform fourth-power improvement closes the
--   best-constant bootstrap.  The proof takes the supremum of all normalized
--   polynomial-calculus ratios, proves that this supremum is itself an admissible
--   global constant, and applies the improvement at that exact constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L392-L488
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L392-L488

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
omit [CompleteSpace E]

theorem isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
    (A : E →L[ℂ] E) (S : Set ℂ) (hspectrum : spectrum ℂ A ⊆ S)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p S)
    (hfour : ∀ K : ℝ, 0 ≤ K →
      (∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p S) →
      ∀ p : Polynomial ℂ,
        ‖Polynomial.aeval A p‖ ^ 4 ≤
          (2 * K ^ 3 + K ^ 2) *
            polynomialSupNorm p S ^ 4) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) S := by sorry
