-- Prove2me | solution 1 for mme_central_binomial_sqrt_loss_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T23:45:19.967854+00:00
-- url     : https://prove2.me/submissions/0eada078-e6d9-45b6-8de5-1eb3ecaf6ba1

import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Theorems.Thm_mme_two_pow_le_succ_mul_central_choose
import Mathlib.Tactic

open Filter Topology

set_option autoImplicit false
set_option warningAsError true

/-- The actual central-binomial finite lower bound retains natural-log rate
log2 per tensor copy after the explicit square-root hashing loss. -/
theorem solution (C delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : ℝ, 0 < x →
        (Nat.choose (2 * n) n : ℝ) *
            Real.exp (-2 * C * Real.sqrt (((n + 1 : ℕ) : ℝ))) ≤ 4 * x →
          (2 * (n : ℝ)) * (Real.log 2 - delta) ≤ Real.log x := by
  have hbudget := mme_log_sqrt_loss_eventually_le_linear
    1 (2 * C) (Real.log 2 + Real.log 4) (2 * delta) (by linarith)
  filter_upwards [hbudget] with n hn
  intro x hx hbound
  have hchoosepos : (0 : ℝ) < (Nat.choose (2 * n) n : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  have hcentral : 2 ^ (2 * n) ≤ (2 * n + 1) * Nat.choose (2 * n) n := by
    simpa using mme_two_pow_le_succ_mul_central_choose (2 * n)
  have hcentralR :
      (2 : ℝ) ^ (2 * n) ≤ (2 * (n : ℝ) + 1) *
        (Nat.choose (2 * n) n : ℝ) := by exact_mod_cast hcentral
  have hlogcentral := Real.log_le_log (by positivity) hcentralR
  rw [Real.log_pow, Real.log_mul (by positivity) hchoosepos.ne'] at hlogcentral
  push_cast at hlogcentral
  have hlogshift := Real.log_le_log (by positivity : 0 < 2 * (n : ℝ) + 1)
    (show 2 * (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlogshift
  have hlogbound := Real.log_le_log
    (mul_pos hchoosepos (Real.exp_pos _)) hbound
  rw [Real.log_mul hchoosepos.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne'] at hlogbound
  simp only [Nat.cast_add, Nat.cast_one] at hlogbound
  nlinarith
