-- Prove2me | Theorems.Thm_natDegree_divByMonic_X_sub_C_eq_sub_one
-- name    : natDegree_divByMonic_X_sub_C_eq_sub_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:58:25.860844+00:00
-- url     : https://prove2.me/theorems/b545fafd-d578-4413-86bb-272d71d43629
-- title:
--   nat Degree div By Monic X sub C eq sub one: nat Degree div By Monic X sub C eq sub one
-- statement:
--   The polynomial divided difference used at `xi` has degree exactly one
--   less, truncated at zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L51-L56
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L51-L56

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem natDegree_divByMonic_X_sub_C_eq_sub_one
    (p : Polynomial ℂ) (xi : ℂ) :
    (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree =
      p.natDegree - 1 := by sorry
