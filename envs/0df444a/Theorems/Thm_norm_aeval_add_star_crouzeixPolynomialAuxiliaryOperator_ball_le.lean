-- Prove2me | Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le
-- name    : norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:01:25.21914+00:00
-- url     : https://prove2.me/theorems/0a6930b8-c146-5022-a177-9252fd7b1fb3
-- title:
--   norm aeval add star crouzeix Polynomial Auxiliary Operator ball le: norm aeval add star crouzeix Polynomial Auxiliary Operator ball le
-- statement:
--   **Disk-model symmetrized Crouzeix–Palencia bound.** For `‖A‖ < R` and the auxiliary operator
--   `G` of the disk `ball 0 R`, `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ R} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L147-L161
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L147-L161

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

theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le (A : E →L[ℂ] E) {R : ℝ}
    (hR : ‖A‖ < R) (p : ℂ[X]) :
    ‖aeval A p + star (crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by sorry
