-- Prove2me | Theorems.Thm_natDegree_divByMonic_X_sub_C_lt
-- name    : natDegree_divByMonic_X_sub_C_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:59:59.348806+00:00
-- url     : https://prove2.me/theorems/bf7aa51a-1fcf-4d80-be52-d1e5c48fff0c
-- title:
--   nat Degree div By Monic X sub C lt: nat Degree div By Monic X sub C lt
-- statement:
--   For a positive-degree polynomial, the divided difference has strictly
--   smaller natural degree.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L60-L64
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L60-L64

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem natDegree_divByMonic_X_sub_C_lt
    (p : Polynomial ℂ) (xi : ℂ) (hp : 0 < p.natDegree) :
    (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree < p.natDegree := by sorry
