-- Prove2me | Theorems.Thm_eval_sub_C_eval_eq_zero
-- name    : eval_sub_C_eval_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:26.938012+00:00
-- url     : https://prove2.me/theorems/d7a277be-827e-46a5-88a3-b6018cf3d1dc
-- title:
--   eval sub C eval eq zero: eval sub C eval eq zero
-- statement:
--   The canonical boundary-point normalization has zero value at `xi`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L141-L143
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L141-L143

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem eval_sub_C_eval_eq_zero (p : Polynomial ℂ) (xi : ℂ) :
    Polynomial.eval xi (p - Polynomial.C (Polynomial.eval xi p)) = 0 := by sorry
