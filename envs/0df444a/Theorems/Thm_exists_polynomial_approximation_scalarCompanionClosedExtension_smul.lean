-- Prove2me | Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_smul
-- name    : exists_polynomial_approximation_scalarCompanionClosedExtension_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:52.762711+00:00
-- url     : https://prove2.me/theorems/e72de7b1-8891-5af0-88e0-13fb8ce064dc
-- title:
--   exists polynomial approximation scalar Companion Closed Extension smul: exists polynomial approximation scalar Companion Closed Extension smul
-- statement:
--   Consequently, a uniform approximation transfers under polynomial scaling
--   with the expected multiplicative error.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2014-L2036
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2014-L2036

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_polynomial_approximation_scalarCompanionClosedExtension_smul
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (S : Set ℂ) (hS : S ⊆ closure Omega.carrier) (epsilon : ℕ → ℝ)
    (happrox : ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          epsilon j) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ S →
        ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              Omega (a • p) z‖ ≤
          ‖a‖ * epsilon j := by sorry
