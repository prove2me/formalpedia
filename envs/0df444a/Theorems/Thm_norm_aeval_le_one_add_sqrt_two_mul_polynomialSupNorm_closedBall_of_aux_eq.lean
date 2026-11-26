-- Prove2me | Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq
-- name    : norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:55.459478+00:00
-- url     : https://prove2.me/theorems/bfc28552-459a-416d-a5b4-4fb3a97f887b
-- title:
--   norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of aux eq: norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of aux eq
-- statement:
--   **Disk-model Crouzeix–Palencia inequality**, given the value of the disk auxiliary operator:
--   if `‖A‖ < R` and the conjugate-polynomial auxiliary operator of `ball 0 R` equals
--   `star (p.eval 0) • 1`, then `‖p(A)‖ ≤ (1 + √2) * sup_{|z| ≤ R} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L168-L177
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L168-L177

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_aux_eq
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X])
    (hG : crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p =
      star (p.eval 0) • (1 : E →L[ℂ] E)) :
    ‖aeval A p‖ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by sorry
