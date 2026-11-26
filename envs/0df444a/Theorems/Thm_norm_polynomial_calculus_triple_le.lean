-- Prove2me | Theorems.Thm_norm_polynomial_calculus_triple_le
-- name    : norm_polynomial_calculus_triple_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:46:06.31583+00:00
-- url     : https://prove2.me/theorems/31c9391b-7bd7-409b-a7b7-50d6639900d6
-- title:
--   norm polynomial calculus triple le: norm polynomial calculus triple le
-- statement:
--   A global polynomial-calculus bound controls the evaluated multiplicative
--   triple by the product of the three compact-set polynomial sup norms.  This is
--   the algebraic approximation bridge needed when the scalar Cauchy companion
--   has itself been represented by a polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L257-L272
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L257-L272

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_polynomial_calculus_triple_le
    (A : E →L[ℂ] E) {K : ℝ} (hK : 0 ≤ K)
    {S : Set ℂ} (hS : IsCompact S)
    (hcalc : ∀ r : Polynomial ℂ,
      ‖Polynomial.aeval A r‖ ≤ K * polynomialSupNorm r S)
    (p q : Polynomial ℂ) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q * Polynomial.aeval A p‖ ≤
      K * (polynomialSupNorm p S ^ 2 * polynomialSupNorm q S) := by sorry
