-- Prove2me | solution 1 for lean_workbook_plus_15041
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:37.041241+00:00
-- url     : https://prove2.me/submissions/3bffff49-072e-42cf-aac9-06f99a59b784

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ n k : ℕ, (n.choose (2 * k + 1)) * (2^(3 * k)) = (n.choose (2 * k + 1)) * (2 * Real.sqrt 2)^(2 * k + 1) / (2 * Real.sqrt 2) := by
  intro n k
  have h2 : (0:ℝ) < 2 * Real.sqrt 2 := by positivity
  have hsq : (2 * Real.sqrt 2) ^ 2 = (8:ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hpow : (2 * Real.sqrt 2) ^ (2 * k + 1) = (2:ℝ) ^ (3 * k) * (2 * Real.sqrt 2) := by
    rw [pow_succ, pow_mul, hsq, pow_mul]
    norm_num
  rw [hpow, eq_div_iff h2.ne']
  ring
