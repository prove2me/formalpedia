-- Prove2me | Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
-- name    : polynomial_eq_zero_of_polynomialSupNorm_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:43.428135+00:00
-- url     : https://prove2.me/theorems/0761933a-6fae-5394-8c9d-e93c713d6757
-- title:
--   polynomial eq zero of polynomial Sup Norm eq zero: polynomial eq zero of polynomial Sup Norm eq zero
-- statement:
--   A complex polynomial with zero sup norm on an infinite compact set is the
--   zero polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L42-L53
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L42-L53

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u

theorem polynomial_eq_zero_of_polynomialSupNorm_eq_zero
    (p : ℂ[X]) {K : Set ℂ} (hK : IsCompact K) (hKinf : K.Infinite)
    (hzero : polynomialSupNorm p K = 0) : p = 0 := by sorry
