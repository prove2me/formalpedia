-- Prove2me | solution 1 for lean_workbook_plus_76550
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:13.193589+00:00
-- url     : https://prove2.me/submissions/0d8b1434-49f8-4b48-845c-0e68448b4e01

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (a : ℝ) (ha : a > 0) :
    Real.sqrt (a ^ 2 + 1 / a) ≥ (a + 3) / (2 * Real.sqrt 2) := by
  have hs := mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ 7 * a + 8 by linarith)
  have hp : ((a + 3) ^ 2 / 8 - a ^ 2) * a ≤ 1 := by nlinarith [hs]
  have hd := (le_div_iff₀ ha).2 hp
  apply Real.le_sqrt_of_sq_le
  calc
    ((a + 3) / (2 * Real.sqrt 2)) ^ 2 = (a + 3) ^ 2 / 8 := by
      norm_num [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ a ^ 2 + 1 / a := by linarith
