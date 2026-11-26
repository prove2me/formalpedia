-- Prove2me | Theorems.Thm_norm_eval_circleMap_le_polynomialSupNorm_closedBall
-- name    : norm_eval_circleMap_le_polynomialSupNorm_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:43.5468+00:00
-- url     : https://prove2.me/theorems/82291b2d-363f-4f08-b0d6-b1e9a493c023
-- title:
--   norm eval circle Map le polynomial Sup Norm closed Ball: norm eval circle Map le polynomial Sup Norm closed Ball
-- statement:
--   On the circle `|z - c| = R` (with `0 ≤ R`), a polynomial is bounded by its sup-norm over the
--   closed disk `closedBall c R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L56-L61
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L56-L61

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

theorem norm_eval_circleMap_le_polynomialSupNorm_closedBall (p : ℂ[X]) (c : ℂ) {R : ℝ}
    (hR : 0 ≤ R) (t : ℝ) :
    ‖p.eval (circleMap c R t)‖ ≤ polynomialSupNorm p (Metric.closedBall c R) := by sorry
