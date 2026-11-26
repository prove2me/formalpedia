-- Prove2me | Theorems.Thm_polynomialSupNorm_mul_mul_le_of_isCompact
-- name    : polynomialSupNorm_mul_mul_le_of_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:23.999982+00:00
-- url     : https://prove2.me/theorems/e7d5e60d-1e9d-467f-a848-b37f631b2382
-- title:
--   polynomial Sup Norm mul mul le of is Compact: polynomial Sup Norm mul mul le of is Compact
-- statement:
--   The compact-set sup norm of the multiplicative triple `p*q*p` is at
--   most `‖p‖²‖q‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L208-L221
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L208-L221

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace

theorem polynomialSupNorm_mul_mul_le_of_isCompact
    {S : Set ℂ} (hS : IsCompact S) (p q : Polynomial ℂ) :
    polynomialSupNorm (p * q * p) S ≤
      polynomialSupNorm p S ^ 2 * polynomialSupNorm q S := by sorry
