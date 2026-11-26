-- Prove2me | Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero
-- name    : polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:37:10.967029+00:00
-- url     : https://prove2.me/theorems/d4be87bb-d209-4a4c-9914-1bcd900c1b7e
-- title:
--   polynomial eq zero of polynomial Sup Norm closed Ball eq zero: polynomial eq zero of polynomial Sup Norm closed Ball eq zero
-- statement:
--   A complex polynomial with zero sup norm on a closed disk of positive
--   radius is the zero polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L57-L62
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L57-L62

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u

theorem polynomial_eq_zero_of_polynomialSupNorm_closedBall_eq_zero
    (p : ℂ[X]) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hzero : polynomialSupNorm p (Metric.closedBall c R) = 0) :
    p = 0 := by sorry
