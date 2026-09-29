-- Prove2me | solution 1 for mme_CW_q6_common_halving_polynomial_loss_le_exp_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:56:04.924644+00:00
-- url     : https://prove2.me/submissions/99863206-b1d2-45c2-962e-a745ec0981f7

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-- The explicit polynomial loss from common-halving extraction is bounded
by a square-root exponential, uniformly in the length. -/
theorem solution (N : ℕ) :
    (((128 * (N + 1) ^ 20 : ℕ) : ℝ)) ≤
      Real.exp ((128 * ((40 : ℕ).factorial : ℝ)) *
        Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let C : ℝ := 128 * ((40 : ℕ).factorial : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx2 : x ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have hx40 : x ^ 40 = (((N + 1 : ℕ) : ℝ)) ^ 20 := by
    calc
      x ^ 40 = (x ^ 2) ^ 20 := by norm_num [← pow_mul]
      _ = (((N + 1 : ℕ) : ℝ)) ^ 20 := by rw [hx2]
  have hC1 : (1 : ℝ) ≤ C := by
    dsimp [C]
    norm_num
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC1
  have hcoeff :
      (128 : ℝ) * ((40 : ℕ).factorial : ℝ) ≤ C ^ 40 := by
    change C ≤ C ^ 40
    calc
      C = C * 1 := by ring
      _ ≤ C * C ^ 39 := by
        gcongr
        exact one_le_pow₀ hC1
      _ = C ^ 40 := by ring
  have hpoly :
      ((128 : ℝ) * (((N + 1 : ℕ) : ℝ)) ^ 20) *
          ((40 : ℕ).factorial : ℝ) ≤ (C * x) ^ 40 := by
    rw [← hx40]
    calc
      ((128 : ℝ) * x ^ 40) * ((40 : ℕ).factorial : ℝ) =
          ((128 : ℝ) * ((40 : ℕ).factorial : ℝ)) * x ^ 40 := by ring
      _ ≤ C ^ 40 * x ^ 40 := by gcongr
      _ = (C * x) ^ 40 := by ring
  have hbase :
      (128 : ℝ) * (((N + 1 : ℕ) : ℝ)) ^ 20 ≤ Real.exp (C * x) := by
    calc
      (128 : ℝ) * (((N + 1 : ℕ) : ℝ)) ^ 20 ≤
          (C * x) ^ 40 / ((40 : ℕ).factorial : ℝ) := by
        apply (le_div_iff₀ (by positivity :
          (0 : ℝ) < ((40 : ℕ).factorial : ℝ))).2
        simpa only [mul_assoc] using hpoly
      _ ≤ Real.exp (C * x) :=
        Real.pow_div_factorial_le_exp (C * x) (mul_nonneg hC0 hx0) 40
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, C, x] using hbase
