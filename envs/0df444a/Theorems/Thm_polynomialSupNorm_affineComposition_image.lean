-- Prove2me | Theorems.Thm_polynomialSupNorm_affineComposition_image
-- name    : polynomialSupNorm_affineComposition_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:29.06639+00:00
-- url     : https://prove2.me/theorems/66f0e3de-4ef9-5aa8-bad3-dd7baf933da0
-- title:
--   polynomial Sup Norm affine Composition image: polynomial Sup Norm affine Composition image
-- statement:
--   The sup-norm of an affine composition on `X` is the original sup-norm on the affine image
--   of `X`. This remains exact for unbounded sets: in that case both conditionally complete suprema
--   use the same unbounded family of values.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L68-L85
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffinePolynomial.lean#L68-L85

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Definitions.Def_Operator_SpectralSet_Basic
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
set_option autoImplicit false
open scoped Polynomial

theorem polynomialSupNorm_affineComposition_image (p : ℂ[X]) (a b : ℂ) (X : Set ℂ) :
    polynomialSupNorm (p.affineComposition a b) X =
      polynomialSupNorm p ((fun z : ℂ => a * z + b) '' X) := by sorry
