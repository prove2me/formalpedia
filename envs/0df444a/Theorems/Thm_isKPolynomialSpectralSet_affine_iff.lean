-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_affine_iff
-- name    : isKPolynomialSpectralSet_affine_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:06.26495+00:00
-- url     : https://prove2.me/theorems/d1ac20d2-1ff5-57c9-a44c-b47ad85920a0
-- title:
--   is KPolynomial Spectral Set affine iff: is KPolynomial Spectral Set affine iff
-- statement:
--   Affine transport is an equivalence for nonzero linear coefficient.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L63-L91
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L63-L91

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem isKPolynomialSpectralSet_affine_iff
    (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsKPolynomialSpectralSet (a • A + b • 1) K
        ((fun z => a * z + b) '' X) ↔
      IsKPolynomialSpectralSet A K X := by sorry
