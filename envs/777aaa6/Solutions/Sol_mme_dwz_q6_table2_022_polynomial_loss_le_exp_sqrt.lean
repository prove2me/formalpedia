-- Prove2me | solution 1 for mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:57:54.730455+00:00
-- url     : https://prove2.me/submissions/9f3d84d5-5900-4b53-8060-203be4321628

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

theorem solution (tau : ℝ) (htau : 0 ≤ tau) (m : ℕ) :
    ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) ^ tau ≤
      Real.exp ((155520 * tau) *
        Real.sqrt (((m + 1 : ℕ) : ℝ))) := by
  let x : ℝ := Real.sqrt (((m + 1 : ℕ) : ℝ))
  let C : ℝ := 155520
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x ^ 2 = (((m + 1 : ℕ) : ℝ)) := by
    dsimp [x]
    exact Real.sq_sqrt (by positivity)
  have hx6 : x ^ 6 = (((m + 1 : ℕ) : ℝ)) ^ 3 := by
    calc
      x ^ 6 = (x ^ 2) ^ 3 := by norm_num [← pow_mul]
      _ = (((m + 1 : ℕ) : ℝ)) ^ 3 := by rw [hx2]
  have hC1 : (1 : ℝ) ≤ C := by norm_num [C]
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC1
  have hCpow5 : (1 : ℝ) ≤ C ^ 5 := one_le_pow₀ hC1
  have hCpow : C ≤ C ^ 6 := by
    calc
      C = C * 1 := by ring
      _ ≤ C * C ^ 5 := by gcongr
      _ = C ^ 6 := by ring
  have hpoly :
      ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) *
          ((6 : ℕ).factorial : ℝ) ≤ (C * x) ^ 6 := by
    calc
      ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) *
            ((6 : ℕ).factorial : ℝ) = C * x ^ 6 := by
        rw [hx6]
        norm_num [C]
        ring
      _ ≤ C ^ 6 * x ^ 6 := by gcongr
      _ = (C * x) ^ 6 := by ring
  have hbase :
      (6 * (((m + 1 : ℕ) : ℝ))) ^ 3 ≤ Real.exp (C * x) := by
    calc
      (6 * (((m + 1 : ℕ) : ℝ))) ^ 3 ≤
          (C * x) ^ 6 / ((6 : ℕ).factorial : ℝ) := by
        apply (le_div_iff₀ (by positivity :
          (0 : ℝ) < ((6 : ℕ).factorial : ℝ))).2
        simpa only [mul_assoc] using hpoly
      _ ≤ Real.exp (C * x) :=
        Real.pow_div_factorial_le_exp (C * x) (mul_nonneg hC0 hx0) 6
  calc
    ((6 * (((m + 1 : ℕ) : ℝ))) ^ 3) ^ tau ≤
        (Real.exp (C * x)) ^ tau :=
      Real.rpow_le_rpow (by positivity) hbase htau
    _ = Real.exp ((155520 * tau) *
          Real.sqrt (((m + 1 : ℕ) : ℝ))) := by
      rw [← Real.exp_mul]
      dsimp only [C, x]
      congr 1
      ring
