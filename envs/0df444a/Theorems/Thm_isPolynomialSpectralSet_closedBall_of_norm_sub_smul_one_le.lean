-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_closedBall_of_norm_sub_smul_one_le
-- name    : isPolynomialSpectralSet_closedBall_of_norm_sub_smul_one_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:31:52.423243+00:00
-- url     : https://prove2.me/theorems/ab0d8cb3-4df6-473f-923d-e8f2cdd2ef25
-- title:
--   is Polynomial Spectral Set closed Ball of norm sub smul one le: is Polynomial Spectral Set closed Ball of norm sub smul one le
-- statement:
--   A disk containing `A` in the centered operator-norm sense is a polynomial spectral set for
--   `A`, with sharp constant `1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L89-L98
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L89-L98

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem isPolynomialSpectralSet_closedBall_of_norm_sub_smul_one_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • 1‖ ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall c R) := by sorry
