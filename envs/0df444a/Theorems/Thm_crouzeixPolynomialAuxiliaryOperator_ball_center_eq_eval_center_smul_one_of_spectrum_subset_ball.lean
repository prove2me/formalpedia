-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
-- name    : crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:22.049957+00:00
-- url     : https://prove2.me/theorems/b1fbffd7-ba32-538e-8555-15f9fee4ecaa
-- title:
--   crouzeix Polynomial Auxiliary Operator ball center eq eval center smul one of spectrum subset ball: crouzeix Polynomial Auxiliary Operator ball center eq eval center smul one of spectrum subset ball
-- statement:
--   The disk auxiliary operator with center `c` under spectral enclosure equals
--   `star (p.eval c) • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L51-L59
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L51-L59

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    (p : ℂ[X]) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c r hr) p =
      star (p.eval c) • (1 : E →L[ℂ] E) := by sorry
