-- Prove2me | Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt
-- name    : norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:40.291317+00:00
-- url     : https://prove2.me/theorems/71155418-8992-5ae8-a62a-871c6ce6ebce
-- title:
--   norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of norm lt: norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of norm lt
-- statement:
--   **Disk-model Crouzeix–Palencia inequality.** If `‖A‖ < R`, then for every polynomial `p`,
--   `‖p(A)‖ ≤ (1 + √2) * sup_{|z| ≤ R} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L183-L187
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L183-L187

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

theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_norm_lt
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by sorry
