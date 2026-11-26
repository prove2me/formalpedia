-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
-- name    : norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:51.103469+00:00
-- url     : https://prove2.me/theorems/f9fd419e-ba81-4900-85a8-ee04b822888c
-- title:
--   norm aeval le polynomial Sup Norm closed Ball of norm sub smul one le: norm aeval le polynomial Sup Norm closed Ball of norm sub smul one le
-- statement:
--   Von Neumann's inequality on a closed disk: if `‖A - cI‖ ≤ R` and `R > 0`, then evaluation
--   at `A` is bounded by the polynomial sup-norm on `closedBall c R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L62-L85
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L62-L85

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem norm_aeval_le_polynomialSupNorm_closedBall_of_norm_sub_smul_one_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • 1‖ ≤ R) (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (Metric.closedBall c R) := by sorry
