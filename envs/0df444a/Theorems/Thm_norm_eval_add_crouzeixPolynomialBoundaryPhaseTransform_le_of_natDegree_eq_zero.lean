-- Prove2me | Theorems.Thm_norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
-- name    : norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:58:29.264804+00:00
-- url     : https://prove2.me/theorems/a275c7ad-9ffa-46b6-9630-41f4fdbfc5db
-- title:
--   norm eval add crouzeix Polynomial Boundary Phase Transform le of nat Degree eq zero: norm eval add crouzeix Polynomial Boundary Phase Transform le of nat Degree eq zero
-- statement:
--   Degree-zero polynomials satisfy the sharp boundary-phase inequality
--   automatically: their divided difference and hence their phase transform
--   vanish.  This is the base case for any induction through the lower-degree
--   phase contour.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L256-L278
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L256-L278

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hp : p.natDegree = 0) (xi : ℂ) :
    ‖star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
