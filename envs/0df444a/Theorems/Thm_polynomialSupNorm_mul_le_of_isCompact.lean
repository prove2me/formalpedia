-- Prove2me | Theorems.Thm_polynomialSupNorm_mul_le_of_isCompact
-- name    : polynomialSupNorm_mul_le_of_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:26.192092+00:00
-- url     : https://prove2.me/theorems/8621eb21-ecdf-48ab-9910-1ed97033cd5e
-- title:
--   polynomial Sup Norm mul le of is Compact: polynomial Sup Norm mul le of is Compact
-- statement:
--   Polynomial sup norms are submultiplicative on compact sets.  Compactness
--   supplies the boundedness needed to compare each point evaluation with the
--   conditionally complete supremum used by `polynomialSupNorm`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L183-L204
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L183-L204

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace

theorem polynomialSupNorm_mul_le_of_isCompact
    {S : Set ℂ} (hS : IsCompact S) (p q : Polynomial ℂ) :
    polynomialSupNorm (p * q) S ≤
      polynomialSupNorm p S * polynomialSupNorm q S := by sorry
