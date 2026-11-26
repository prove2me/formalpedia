-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_divByMonic
-- name    : crouzeixPolynomialScalarCompanionBoundaryValue_eq_divByMonic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:42:43.479442+00:00
-- url     : https://prove2.me/theorems/649909a5-9c64-4df6-8b21-fe55f5890267
-- title:
--   crouzeix Polynomial Scalar Companion Boundary Value eq div By Monic: crouzeix Polynomial Scalar Companion Boundary Value eq div By Monic
-- statement:
--   The explicit Plemelj boundary value consists of the conjugate boundary
--   datum and the phase-weighted contour of a lower-degree polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L113-L126
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L113-L126

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionBoundaryValue_eq_divByMonic
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          contourIntegral
            (fun sigma ↦
              star (sigma - xi) *
                star (Polynomial.eval sigma
                  (p /ₘ (Polynomial.X - Polynomial.C xi))) *
                (sigma - xi)⁻¹)
            Omega.boundaryParam := by sorry
