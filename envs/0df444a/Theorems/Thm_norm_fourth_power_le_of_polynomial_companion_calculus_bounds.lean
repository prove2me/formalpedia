-- Prove2me | Theorems.Thm_norm_fourth_power_le_of_polynomial_companion_calculus_bounds
-- name    : norm_fourth_power_le_of_polynomial_companion_calculus_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:35:17.374366+00:00
-- url     : https://prove2.me/theorems/1839bbff-9636-5cda-8600-3bb64135068d
-- title:
--   norm fourth power le of polynomial companion calculus bounds: norm fourth power le of polynomial companion calculus bounds
-- statement:
--   The published fourth-power estimate specialized to a polynomial
--   companion `q`.  A global calculus constant bounds both `p(A)` and the
--   multiplicative triple `(p*q*p)(A)`; compact-set sup-norm
--   submultiplicativity and `‖p‖ₛ,‖q‖ₛ ≤ m` give the required `K m³` bound.
--
--   The analytic Crouzeix--Palencia companion need not be a polynomial, so using
--   this theorem for that companion still requires a norm-preserving polynomial
--   approximation argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L284-L306
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L284-L306

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem norm_fourth_power_le_of_polynomial_companion_calculus_bounds
    (A : E →L[ℂ] E) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p q : Polynomial ℂ)
    (hp : polynomialSupNorm p S ≤ m)
    (hq : polynomialSupNorm q S ≤ m)
    (hsymm : ‖Polynomial.aeval A p + star (Polynomial.aeval A q)‖ ≤ 2 * m) :
    ‖Polynomial.aeval A p‖ ^ 4 ≤
      (2 * K ^ 3 + K ^ 2) * m ^ 4 := by sorry
