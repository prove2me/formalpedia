-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_closedBall
-- name    : isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_closedBall
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:51:38.805785+00:00
-- url     : https://prove2.me/theorems/d0d4ef75-7b28-5acd-9f30-198df70a6df6
-- title:
--   is KPolynomial Spectral Set three closed Ball of closure numerical Range subset closed Ball: is KPolynomial Spectral Set three closed Ball of closure numerical Range subset closed Ball
-- statement:
--   **Closed disks containing the numerical range are 3-polynomial-spectral sets.**
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L158-L164
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralAuxiliaryCenter.lean#L158-L164

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isKPolynomialSpectralSet_three_closedBall_of_closure_numericalRange_subset_closedBall
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hW : closure (numericalRange A) ⊆ Metric.closedBall c r) :
    IsKPolynomialSpectralSet A 3 (Metric.closedBall c r) := by sorry
