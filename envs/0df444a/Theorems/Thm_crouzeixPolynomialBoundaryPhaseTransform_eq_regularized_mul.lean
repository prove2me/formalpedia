-- Prove2me | Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul
-- name    : crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:58:37.848811+00:00
-- url     : https://prove2.me/theorems/691c6571-35ee-4276-a7e2-2a85ea573f3e
-- title:
--   crouzeix Polynomial Boundary Phase Transform eq regularized mul: crouzeix Polynomial Boundary Phase Transform eq regularized mul
-- statement:
--   The phase transform of `q` is itself the regularized self-value of the
--   polynomial `(X - C xi) * q`.  This realizes the lower-degree contour as the
--   same cancelled Cauchy construction already used by the Plemelj split.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L157-L166
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L157-L166

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialBoundaryPhaseTransform_eq_regularized_mul
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi q =
      crouzeixPolynomialScalarCompanionRegularized Omega
        ((Polynomial.X - Polynomial.C xi) * q) xi xi := by sorry
