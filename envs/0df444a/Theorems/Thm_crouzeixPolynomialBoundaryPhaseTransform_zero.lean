-- Prove2me | Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
-- name    : crouzeixPolynomialBoundaryPhaseTransform_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:27.066255+00:00
-- url     : https://prove2.me/theorems/05d12c67-4954-46a5-95ea-eb32fe7160da
-- title:
--   crouzeix Polynomial Boundary Phase Transform zero: crouzeix Polynomial Boundary Phase Transform zero
-- statement:
--   The boundary phase transform of the zero polynomial vanishes.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L245-L250
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L245-L250

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialBoundaryPhaseTransform_zero
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi 0 = 0 := by sorry
