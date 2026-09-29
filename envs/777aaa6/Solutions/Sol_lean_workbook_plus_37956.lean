-- Prove2me | solution 1 for lean_workbook_plus_37956
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:55:54.246922+00:00
-- url     : https://prove2.me/submissions/59ed1a01-ddd7-4beb-b1aa-c6c0f7366a3b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a^2 + 2 * b^2 + c^2 = a^3 + 2 * b^3 + c^3) : a + 2 * b + c ≤ 4 := by
  have h1 := mul_nonneg (sq_nonneg (a-1)) (show 0≤a+1 by linarith [ha.1])
  have h2 := mul_nonneg (sq_nonneg (b-1)) (show 0≤b+1 by linarith [ha.2.1])
  have h3 := mul_nonneg (sq_nonneg (c-1)) (show 0≤c+1 by linarith [ha.2.2])
  nlinarith only [h1,h2,h3,hab]
