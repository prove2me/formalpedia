-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
-- name    : crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:55.968976+00:00
-- url     : https://prove2.me/theorems/0a664e85-473f-4dab-8969-f59efd2a0463
-- title:
--   crouzeix Polynomial Scalar Companion Regularized self eq div By Monic: crouzeix Polynomial Scalar Companion Regularized self eq div By Monic
-- statement:
--   The regularized self-value is exactly a phase-weighted contour of the
--   strictly lower-degree divided difference.  The factor
--   `star (sigma - xi) * (sigma - xi)⁻¹` has norm one away from its removable
--   zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L70-L109
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L70-L109

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦
            star (sigma - xi) *
              star (Polynomial.eval sigma
                (p /ₘ (Polynomial.X - Polynomial.C xi))) *
              (sigma - xi)⁻¹)
          Omega.boundaryParam := by sorry
