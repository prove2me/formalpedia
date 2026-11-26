-- Prove2me | Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_add
-- name    : crouzeixPolynomialBoundaryPhaseTransform_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:49.75208+00:00
-- url     : https://prove2.me/theorems/73b5c0aa-6cae-5c78-858f-ea13d50cea21
-- title:
--   crouzeix Polynomial Boundary Phase Transform add: crouzeix Polynomial Boundary Phase Transform add
-- statement:
--   The boundary phase transform is additive in its polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L198-L221
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L198-L221

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialBoundaryPhaseTransform_add
    (Omega : SmoothJordanDomain) (xi : ℂ) (p q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi (p + q) =
      crouzeixPolynomialBoundaryPhaseTransform Omega xi p +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi q := by sorry
