-- Prove2me | Theorems.Thm_polynomialSupNorm_C_of_nonempty
-- name    : polynomialSupNorm_C_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:33.487032+00:00
-- url     : https://prove2.me/theorems/cf2c43e5-61de-5c6c-9146-672669ebb74a
-- title:
--   polynomial Sup Norm C of nonempty: polynomial Sup Norm C of nonempty
-- statement:
--   The polynomial sup norm of `C a` on a nonempty set is `‖a‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L34-L48
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductBase.lean#L34-L48

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem polynomialSupNorm_C_of_nonempty (a : ℂ) {K : Set ℂ}
    (hK : K.Nonempty) : polynomialSupNorm (Polynomial.C a) K = ‖a‖ := by sorry
