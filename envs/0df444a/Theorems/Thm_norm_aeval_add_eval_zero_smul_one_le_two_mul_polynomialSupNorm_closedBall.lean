-- Prove2me | Theorems.Thm_norm_aeval_add_eval_zero_smul_one_le_two_mul_polynomialSupNorm_closedBall
-- name    : norm_aeval_add_eval_zero_smul_one_le_two_mul_polynomialSupNorm_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:12.075595+00:00
-- url     : https://prove2.me/theorems/3f1e8499-6ccc-5395-854f-066ac60e695b
-- title:
--   norm aeval add eval zero smul one le two mul polynomial Sup Norm closed Ball: norm aeval add eval zero smul one le two mul polynomial Sup Norm closed Ball
-- statement:
--   If the closure of the numerical range lies inside a centered open disk,
--   the symmetrized Crouzeix--Palencia estimate can be written without an
--   auxiliary-operator symbol: its adjoint is simply `p.eval 0 • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliary.lean#L136-L148
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliary.lean#L136-L148

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_add_eval_zero_smul_one_le_two_mul_polynomialSupNorm_closedBall
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) r) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p + Polynomial.eval 0 p • (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) r) := by sorry
