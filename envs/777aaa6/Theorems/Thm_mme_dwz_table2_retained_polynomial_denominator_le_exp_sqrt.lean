-- Prove2me | Theorems.Thm_mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt
-- name    : mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:35:51.221919+00:00
-- url     : https://prove2.me/theorems/a8e9378f-fc63-4ab5-a2cf-1988d35b508c
-- title:
--   Explicit square-root-exponential bound for the Table-2 polynomial loss
-- statement:
--   Let x=L+1 and let D be the exact polynomial denominator arising from the two Table-2 hashing branches: D=32 max{(6x)^15(6x)^5x^15,(6x)^5(6x)^9}. With the explicit constant B=32·6^20·70!, one has D≤exp(B√x) for every natural L. This turns the full finite polynomial loss into a source-faithful square-root-exponential loss without asymptotic notation.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the explicit polynomial factors in Equations (21) and (25), Section 6.2, printed pp. 53-59; https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 400000

theorem mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt
    (L : ℕ) :
    let x : ℝ := (((L + 1 : ℕ) : ℝ))
    let jointPoly : ℝ := (6 * x) ^ 15
    let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
    let zPoly : ℝ := (6 * x) ^ 5
    let compatibilityPoly : ℝ := (6 * x) ^ 9
    let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
    32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly) ≤
      Real.exp (B * Real.sqrt x) := by
  sorry
