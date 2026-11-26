-- Prove2me | Theorems.Thm_closure_translate_linearImage_complexMulRealEquiv
-- name    : closure_translate_linearImage_complexMulRealEquiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:58:42.846792+00:00
-- url     : https://prove2.me/theorems/4f93b813-8713-4d09-9a33-dd21a09aaa27
-- title:
--   closure translate linear Image complex Mul Real Equiv: closure translate linear Image complex Mul Real Equiv
-- statement:
--   The closure of a smooth Jordan carrier transported by a complex
--   similarity is the similarity image of the original closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L32-L59
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L32-L59

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem closure_translate_linearImage_complexMulRealEquiv
    (Omega : SmoothJordanDomain) (c a : ℂ) (ha : a ≠ 0) :
    closure
        (((Omega.linearImage (complexMulRealEquiv a ha)).translate c).carrier) =
      (fun z => c + a * z) '' closure Omega.carrier := by sorry
