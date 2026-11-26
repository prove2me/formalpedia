-- Prove2me | Theorems.Thm_norm_aeval_pow_le_iSup_numericalRange_of_isStarNormal
-- name    : norm_aeval_pow_le_iSup_numericalRange_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:08.642614+00:00
-- url     : https://prove2.me/theorems/a52d5ee7-4a58-4a86-8af8-e83aff8a72a5
-- title:
--   norm aeval pow le i Sup numerical Range of is Star Normal: norm aeval pow le i Sup numerical Range of is Star Normal
-- statement:
--   Powers in the polynomial functional calculus of a normal operator
--   satisfy the sharp constant-one bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L58-L64
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L58-L64

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_pow_le_iSup_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (p : ℂ[X]) (n : ℕ) :
    ‖Polynomial.aeval A p ^ n‖ ≤
      ⨆ z ∈ numericalRange A, ‖Polynomial.eval z p ^ n‖ := by sorry
