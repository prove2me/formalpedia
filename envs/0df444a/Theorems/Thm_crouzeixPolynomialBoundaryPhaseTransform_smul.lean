-- Prove2me | Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_smul
-- name    : crouzeixPolynomialBoundaryPhaseTransform_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:58:33.418884+00:00
-- url     : https://prove2.me/theorems/070a4cde-54f4-4aee-aff3-f090231365cd
-- title:
--   crouzeix Polynomial Boundary Phase Transform smul: crouzeix Polynomial Boundary Phase Transform smul
-- statement:
--   The boundary phase transform is conjugate-homogeneous in its polynomial
--   argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L225-L242
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L225-L242

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialBoundaryPhaseTransform_smul
    (Omega : SmoothJordanDomain) (xi a : ℂ) (q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi (a • q) =
      star a * crouzeixPolynomialBoundaryPhaseTransform Omega xi q := by sorry
