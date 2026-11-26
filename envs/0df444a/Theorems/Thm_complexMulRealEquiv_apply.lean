-- Prove2me | Theorems.Thm_complexMulRealEquiv_apply
-- name    : complexMulRealEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:01.201629+00:00
-- url     : https://prove2.me/theorems/16e03b08-e97b-4777-8c76-1c5c6f99f832
-- title:
--   complex Mul Real Equiv apply: complex Mul Real Equiv apply
-- statement:
--   The complex Mul Real Equiv apply construction uses the complex Mul Real Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L26-L28
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L26-L28

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem complexMulRealEquiv_apply (a : ℂ) (ha : a ≠ 0)
    (z : ℂ) :
    complexMulRealEquiv a ha z = a * z := by sorry

attribute [defeq] complexMulRealEquiv_apply
