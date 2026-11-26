-- Prove2me | Theorems.Thm_spectrum_smul_add_smul_one
-- name    : spectrum_smul_add_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:03.405657+00:00
-- url     : https://prove2.me/theorems/f82c9f00-4457-566d-93c8-666712478d72
-- title:
--   spectrum smul add smul one: spectrum smul add smul one
-- statement:
--   The spectrum commutes with an invertible affine change of an operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L16-L37
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AffineSpectralSet.lean#L16-L37

import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_AffineSpectralSet
set_option autoImplicit false
open Set
open scoped InnerProductSpace Pointwise Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem spectrum_smul_add_smul_one
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    spectrum ℂ (a • A + b • 1) =
      (fun z => a * z + b) '' spectrum ℂ A := by sorry
