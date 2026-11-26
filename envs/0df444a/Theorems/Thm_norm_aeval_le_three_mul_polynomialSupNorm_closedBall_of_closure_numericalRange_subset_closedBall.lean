-- Prove2me | Theorems.Thm_norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_closedBall
-- name    : norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:50.190793+00:00
-- url     : https://prove2.me/theorems/8ab8a3f5-a011-4799-9da1-fe80eab58b93
-- title:
--   norm aeval le three mul polynomial Sup Norm closed Ball of closure numerical Range subset closed Ball: norm aeval le three mul polynomial Sup Norm closed Ball of closure numerical Range subset closed
-- statement:
--   If `closure W(A) ⊆ closedBall c r` with `0 ≤ r`, then `‖p(A)‖ ≤ 3 * sup_{|z - c| ≤ r} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L128-L155
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L128-L155

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hW : closure (numericalRange A) ⊆ Metric.closedBall c r) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (Metric.closedBall c r) := by sorry
