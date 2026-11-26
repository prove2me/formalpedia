-- Prove2me | Theorems.Thm_exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
-- name    : exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:22.258372+00:00
-- url     : https://prove2.me/theorems/74f15fd1-ea7d-495e-a9d0-5592d6af095b
-- title:
--   exists polynomial approximation scalar Companion Closed Extension add C: exists polynomial approximation scalar Companion Closed Extension add C
-- statement:
--   Any uniform polynomial approximation of a canonical companion transfers,
--   with exactly the same error, after adding a constant to the source
--   polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1967-L1991
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1967-L1991

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem exists_polynomial_approximation_scalarCompanionClosedExtension_add_C
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
              Omega (p + Polynomial.C a) z‖ ≤
          epsilon j := by sorry
