-- Prove2me | Theorems.Thm_polynomial_auxiliary_bounds_of_normalized_closedBall
-- name    : polynomial_auxiliary_bounds_of_normalized_closedBall
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:37:20.035305+00:00
-- url     : https://prove2.me/theorems/ffb13a81-b956-5670-abe6-bbe516efacdd
-- title:
--   polynomial auxiliary bounds of normalized closed Ball: polynomial auxiliary bounds of normalized closed Ball
-- statement:
--   On a closed disk of positive radius, normalized sharp auxiliary bounds
--   imply the correctly scaled bounds for every polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L109-L126
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L109-L126

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem polynomial_auxiliary_bounds_of_normalized_closedBall
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (c : ℂ) {R : ℝ}
    (hR : 0 < R) (p : Polynomial ℂ)
    (hnormalized : ∀ q : Polynomial ℂ,
      polynomialSupNorm q (Metric.closedBall c R) = 1 →
        ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
          2 * polynomialSupNorm p (Metric.closedBall c R) ∧
      ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          polynomialSupNorm p (Metric.closedBall c R) ^ 2 := by sorry
