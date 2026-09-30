-- Prove2me | solution 1 for lean_workbook_plus_37439
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:10.884939+00:00
-- url     : https://prove2.me/submissions/28ce0d66-3b6a-441b-b17d-e67f7db74586

import Mathlib
set_option autoImplicit false

theorem solution  (a b : ℝ)
  (h₀ : a * b = 9)
  (h₁ : a + b = 12) :
  |a - b| = 6 * Real.sqrt 3   := by
  have he : (a - b) ^ 2 = 108 := by
    calc
      (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
      _ = 108 := by rw [h₀, h₁]; norm_num
  apply (sq_eq_sq₀ (abs_nonneg (a - b)) (by positivity : 0 ≤ 6 * Real.sqrt 3)).mp
  norm_num [sq_abs, mul_pow, Real.sq_sqrt, he]

#print axioms solution
