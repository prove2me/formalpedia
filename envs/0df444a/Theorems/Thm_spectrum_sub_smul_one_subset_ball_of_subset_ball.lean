-- Prove2me | Theorems.Thm_spectrum_sub_smul_one_subset_ball_of_subset_ball
-- name    : spectrum_sub_smul_one_subset_ball_of_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:17.344924+00:00
-- url     : https://prove2.me/theorems/17fde480-b0f1-4d26-9420-3a5ab6d93079
-- title:
--   spectrum sub smul one subset ball of subset ball: spectrum sub smul one subset ball of subset ball
-- statement:
--   Translating the spectrum: if `σ(A) ⊆ ball c r` then `σ(A - c • 1) ⊆ ball 0 r`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L37-L47
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L37-L47

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]

theorem spectrum_sub_smul_one_subset_ball_of_subset_ball (A : E →L[ℂ] E) {c : ℂ} {r : ℝ}
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    spectrum ℂ (A - c • (1 : E →L[ℂ] E)) ⊆ Metric.ball (0 : ℂ) r := by sorry
