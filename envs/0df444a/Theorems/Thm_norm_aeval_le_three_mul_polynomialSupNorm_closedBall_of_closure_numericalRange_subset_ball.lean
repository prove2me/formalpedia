-- Prove2me | Theorems.Thm_norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
-- name    : norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:27.971554+00:00
-- url     : https://prove2.me/theorems/9da8f76f-5aa0-4cae-8075-a73e31e1a7be
-- title:
--   norm aeval le three mul polynomial Sup Norm closed Ball of closure numerical Range subset ball: norm aeval le three mul polynomial Sup Norm closed Ball of closure numerical Range subset ball
-- statement:
--   If `closure W(A) ⊆ ball c r`, then `‖p(A)‖ ≤ 3 * sup_{|z - c| ≤ r} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L79-L98
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L79-L98

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (Metric.closedBall c r) := by sorry
