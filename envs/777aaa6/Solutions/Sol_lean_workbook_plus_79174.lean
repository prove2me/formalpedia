-- Prove2me | solution 1 for lean_workbook_plus_79174
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:31:16.081658+00:00
-- url     : https://prove2.me/submissions/80a4b91e-52ec-4b29-a3a8-d4a81eb03319

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ y : ℝ, y ∈ Set.Icc 0 1 →
    (2 * y ^ 2 - y) / 3 + 1 ≥
      (4 * Real.sqrt 3) / 9 * y * Real.sqrt (1 + 2 * y) := by
  intro y hy
  have hy0 : 0 ≤ y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have ht := Real.sq_sqrt (show 0 ≤ 1 + 2 * y by linarith [hy.1])
  have hp : ((4 * Real.sqrt 3) / 9 * y * Real.sqrt (1 + 2 * y)) ^ 2 =
      (16 : ℝ) / 27 * y ^ 2 * (1 + 2 * y) := by
    calc
      _ = (16 : ℝ) / 81 * y ^ 2 * (Real.sqrt 3) ^ 2 *
          (Real.sqrt (1 + 2 * y)) ^ 2 := by ring
      _ = _ := by rw [hs, ht]; ring
  have hleft : 0 ≤ (2 * y ^ 2 - y) / 3 + 1 := by nlinarith [hy.2]
  apply (sq_le_sq₀ (by positivity) hleft).mp
  rw [hp]
  have hfactor : 0 ≤ (1 - y) *
      (12 * y ^ 2 * (1 - y) + 20 * y ^ 2 + 9 * y + 27) := by
    apply mul_nonneg (by linarith [hy.2])
    have : 0 ≤ 1 - y := by linarith [hy.2]
    positivity
  nlinarith

#print axioms solution
