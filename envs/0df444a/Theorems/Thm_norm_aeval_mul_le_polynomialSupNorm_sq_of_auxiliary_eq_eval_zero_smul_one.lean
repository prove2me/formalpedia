-- Prove2me | Theorems.Thm_norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
-- name    : norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:36.804104+00:00
-- url     : https://prove2.me/theorems/2490b625-9be2-5e84-b5d1-2e83711973b0
-- title:
--   norm aeval mul le polynomial Sup Norm sq of auxiliary eq eval zero smul one: norm aeval mul le polynomial Sup Norm sq of auxiliary eq eval zero smul one
-- statement:
--   On a centered disk, the scalar auxiliary identification
--   `G = star (p.eval 0) • 1` implies the sharp L4.2e product estimate.  The
--   subsingleton branch makes the result valid for the zero Hilbert space, where
--   the continuous-linear-map algebra does not have `NormOneClass`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean#L73-L102
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleProduct.lean#L73-L102

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_CircleProduct
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_mul_le_polynomialSupNorm_sq_of_auxiliary_eq_eval_zero_smul_one
    (A : E →L[ℂ] E) {R : ℝ} (hR : 0 < R) (hA : ‖A‖ ≤ R)
    (p : Polynomial ℂ) (G : E →L[ℂ] E)
    (hG : G = star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E)) :
    ‖Polynomial.aeval A p * G‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) ^ 2 := by sorry
