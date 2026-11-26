-- Prove2me | Theorems.Thm_homothety_apply_eq_const_add_mul
-- name    : homothety_apply_eq_const_add_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:18.242558+00:00
-- url     : https://prove2.me/theorems/7c81bf44-56bf-53fd-921c-d4498c76bda7
-- title:
--   homothety apply eq const add mul: homothety apply eq const add mul
-- statement:
--   A real homothety written as a translation followed by scalar
--   multiplication.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L98-L104
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSimilarity.lean#L98-L104

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem homothety_apply_eq_const_add_mul (c z : ℂ) (r : ℝ) :
    AffineMap.homothety c r z = (1 - r) • c + (r : ℂ) * z := by sorry
