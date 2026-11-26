-- Prove2me | Theorems.Thm_isPolynomialSpectralSet_affine_iff
-- name    : isPolynomialSpectralSet_affine_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:34.52837+00:00
-- url     : https://prove2.me/theorems/7f2cd1d8-4097-5372-9d4e-cb8df8d736f5
-- title:
--   is Polynomial Spectral Set affine iff: is Polynomial Spectral Set affine iff
-- statement:
--   Constant-one polynomial spectral sets are invariant under invertible
--   affine changes.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L105-L111
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L105-L111

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isPolynomialSpectralSet_affine_iff
    (A : E →L[ℂ] E) (X : Set ℂ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsPolynomialSpectralSet (a • A + b • 1)
        ((fun z => a * z + b) '' X) ↔
      IsPolynomialSpectralSet A X := by sorry
