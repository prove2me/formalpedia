-- Prove2me | Theorems.Thm_norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
-- name    : norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:37.397797+00:00
-- url     : https://prove2.me/theorems/be9fcdfc-6d8e-5a61-bd05-dd32ddfce37e
-- title:
--   norm aeval add eval center smul one le of closure numerical Range subset ball: norm aeval add eval center smul one le of closure numerical Range subset ball
-- statement:
--   **Classical symmetrized bound for a disk containing the numerical range**: if
--   `closure W(A) ⊆ ball c r`, then `‖p(A) + p(c) • 1‖ ≤ 2 * sup_{|z - c| ≤ r} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L63-L74
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L63-L74

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p + (p.eval c) • (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall c r) := by sorry
