-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_closedBall_of_isStarNormal_of_centered_numericalRadius_le
-- name    : norm_aeval_le_polynomialSupNorm_closedBall_of_isStarNormal_of_centered_numericalRadius_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:13:59.715668+00:00
-- url     : https://prove2.me/theorems/31132dee-4822-4a4a-9c53-de70448b53f1
-- title:
--   norm aeval le polynomial Sup Norm closed Ball of is Star Normal of centered numerical Radius le: norm aeval le polynomial Sup Norm closed Ball of is Star Normal of centered numerical Radius le
-- statement:
--   Direct constant-one polynomial bound for a normal operator on any disk
--   whose radius dominates `w(A-cI)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L130-L137
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L130-L137

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_le_polynomialSupNorm_closedBall_of_isStarNormal_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (Metric.closedBall c R) := by sorry
