-- Prove2me | Theorems.Thm_norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_centered_numericalRadius_le
-- name    : norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_centered_numericalRadius_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:13:49.58181+00:00
-- url     : https://prove2.me/theorems/1f53684c-dc72-446a-8c65-36f608e2a7e5
-- title:
--   norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of centered numerical Radius le: norm aeval le one add sqrt two mul polynomial Sup Norm closed Ball of centered numerical Radius le
-- statement:
--   Direct polynomial form of the Crouzeix--Palencia bound on any disk whose
--   radius dominates `w(A-cI)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L119-L126
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralSetSuperset.lean#L119-L126

import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
import Definitions.Def_Operator_Crouzeix_SpectralSetMonotone
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Definitions.Def_Operator_Crouzeix_SpectralSetSuperset
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_le_one_add_sqrt_two_mul_polynomialSupNorm_closedBall_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) := by sorry
