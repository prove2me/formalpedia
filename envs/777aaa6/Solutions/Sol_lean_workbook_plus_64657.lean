-- Prove2me | solution 1 for lean_workbook_plus_64657
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:52.047266+00:00
-- url     : https://prove2.me/submissions/087cdaee-0d31-4e13-bad3-6440721d96e8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) (hx : (x - Real.sqrt 3) ^ 3 = 64) : x = 4 + Real.sqrt 3 := by
  let t := x - Real.sqrt 3
  have ht : t ^ 3 = 64 := hx
  have hf : (t - 4) * (t ^ 2 + 4 * t + 16) = 0 := by nlinarith
  have hp : 0 < t ^ 2 + 4 * t + 16 := by nlinarith [sq_nonneg (t + 2)]
  have he : t = 4 := by
    rcases mul_eq_zero.mp hf with he | he
    · linarith
    · linarith
  dsimp [t] at he
  linarith

#print axioms solution
