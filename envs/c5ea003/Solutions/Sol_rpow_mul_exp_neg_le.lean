-- Prove2me | solution 1 for rpow_mul_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:22:51.641535+00:00
-- url     : https://prove2.me/submissions/c57c92ab-0be8-4523-b655-6d3e8c73850b

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem solution (q lam x : ℝ) (hq : 0 < q) (hlam : 0 < lam) (hx : 0 ≤ x) :
    x ^ q * Real.exp (-(lam * x)) ≤ (q / (lam * Real.exp 1)) ^ q := by
  -- Work in logs (both sides positive when x>0; x=0 handled separately).
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- x = 0 : LHS = 0^q * 1 = 0 ≤ RHS (RHS > 0).
    rw [← hx0]
    rw [Real.zero_rpow (ne_of_gt hq)]
    simp only [zero_mul]
    positivity
  · -- x > 0
    have hRpos : 0 < q / (lam * Real.exp 1) := by positivity
    have hLpos : 0 < x ^ q * Real.exp (-(lam * x)) := by
      have := Real.rpow_pos_of_pos hxpos q
      positivity
    rw [← Real.log_le_log_iff hLpos (Real.rpow_pos_of_pos hRpos q)]
    -- log LHS = q log x - lam x ;  log RHS = q (log q - log lam - 1)
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hxpos q)) (ne_of_gt (Real.exp_pos _))]
    rw [Real.log_rpow hxpos, Real.log_exp, Real.log_rpow hRpos]
    -- goal: q*log x + (-(lam x)) ≤ q * log(q/(lam e))
    -- log(q/(lam e)) = log q - log(lam) - 1
    have hlogR : Real.log (q / (lam * Real.exp 1)) = Real.log q - Real.log lam - 1 := by
      rw [Real.log_div (ne_of_gt hq) (by positivity),
          Real.log_mul (ne_of_gt hlam) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
      ring
    rw [hlogR]
    -- Need: q log x - lam x ≤ q(log q - log lam - 1)
    -- ⟺ lam x ≥ q log x - q log q + q log lam + q = q(log(lam x/q)) + q  ⟺ lam x/q ≥ log(lam x/q)+1
    -- u := lam x / q > 0; use log u ≤ u - 1.
    set u := lam * x / q with hu
    have hupos : 0 < u := by rw [hu]; positivity
    have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    -- log u = log lam + log x - log q
    have hlu : Real.log u = Real.log lam + Real.log x - Real.log q := by
      rw [hu, Real.log_div (by positivity) (ne_of_gt hq),
          Real.log_mul (ne_of_gt hlam) (ne_of_gt hxpos)]
    rw [hlu] at hlogu
    -- hlogu : log lam + log x - log q ≤ lam x/q - 1.  Multiply by q>0.
    have := mul_le_mul_of_nonneg_left hlogu (le_of_lt hq)
    -- q(log lam + log x - log q) ≤ q(lam x/q - 1) = lam x - q
    have hrhs : q * (lam * x / q - 1) = lam * x - q := by field_simp
    rw [hrhs] at this
    nlinarith [this]
