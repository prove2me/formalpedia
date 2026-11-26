-- Prove2me | Theorems.Thm_exists_uniform_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
-- name    : exists_uniform_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:40.265818+00:00
-- url     : https://prove2.me/theorems/4c39d9c5-0da1-58eb-a46a-aa42ec7be30d
-- title:
--   exists uniform norm crouzeix Polynomial Scalar Companion Boundary Value le: exists uniform norm crouzeix Polynomial Scalar Companion Boundary Value le
-- statement:
--   A single domain-only speed constant gives the preceding boundary-value
--   bound for every polynomial and every frontier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L509-L523
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L509-L523

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem exists_uniform_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (xi : ℂ),
      xi ∈ frontier Omega.carrier →
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (2 * Real.pi *
              (D * polynomialSupNorm
                (p /ₘ (Polynomial.X - Polynomial.C xi))
                (frontier Omega.carrier))) := by sorry
