-- Prove2me | Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_affine
-- name    : exists_polynomial_approximation_scalarCompanionClosedExtension_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:53.629869+00:00
-- url     : https://prove2.me/theorems/e0da07a3-63d3-5fcc-a021-6b722f34fc14
-- title:
--   exists polynomial approximation scalar Companion Closed Extension affine: exists polynomial approximation scalar Companion Closed Extension affine
-- statement:
--   Uniform approximation is therefore stable under the full conjugate-affine
--   action on canonical companions.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2040-L2062
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2040-L2062

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_polynomial_approximation_scalarCompanionClosedExtension_affine
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a b : ℂ)
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
              Omega (a • p + Polynomial.C b) z‖ ≤
          ‖a‖ * epsilon j := by sorry
