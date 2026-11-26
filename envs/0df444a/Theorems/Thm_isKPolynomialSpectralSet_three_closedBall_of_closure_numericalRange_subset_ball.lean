-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_ball
-- name    : isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:20.045544+00:00
-- url     : https://prove2.me/theorems/bfaf8e0b-d2e7-53ad-9de1-b8d47bcd774c
-- title:
--   is KPolynomial Spectral Set three closed Ball of closure numerical Range subset ball: is KPolynomial Spectral Set three closed Ball of closure numerical Range subset ball
-- statement:
--   **Disks containing the numerical range are 3-polynomial-spectral sets**: if
--   `closure W(A) ⊆ ball c r`, then `closedBall c r` is a `3`-polynomial-spectral set for `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L102-L108
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L102-L108

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_ball
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) :
    IsKPolynomialSpectralSet A 3 (Metric.closedBall c r) := by sorry
