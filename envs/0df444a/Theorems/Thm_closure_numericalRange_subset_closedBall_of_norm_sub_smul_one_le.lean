-- Prove2me | Theorems.Thm_closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le
-- name    : closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:59:42.285713+00:00
-- url     : https://prove2.me/theorems/b27b4315-cc21-5294-9c1f-7cdfb7e629aa
-- title:
--   closure numerical Range subset closed Ball of norm sub smul one le: closure numerical Range subset closed Ball of norm sub smul one le
-- statement:
--   If `A - cI` has norm at most `R`, then the closure of the numerical range of `A` lies in the
--   closed disk with center `c` and radius `R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L42-L56
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineDisk.lean#L42-L56

import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_AffineDisk
set_option autoImplicit false
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem closure_numericalRange_subset_closedBall_of_norm_sub_smul_one_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • 1‖ ≤ R) :
    closure (numericalRange A) ⊆ Metric.closedBall c R := by sorry
