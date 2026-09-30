-- Prove2me | solution 1 for lean_workbook_plus_70226
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:05.544853+00:00
-- url     : https://prove2.me/submissions/238dcdbf-c6f5-4457-91a9-3c96f28b9863

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (s : ℝ) (hs : s ≥ 3) :
    (3 * s) / (2 * s + 3) ≤ s / Real.sqrt (s + 6) := by
  have hroot : 0 < Real.sqrt (s + 6) := Real.sqrt_pos.2 (by linarith)
  have hbound : Real.sqrt (s + 6) ≤ (2 * s + 3) / 3 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (2 * s + 3) / 3)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ s - 3) (by linarith : 0 ≤ 4 * s + 15)]
  have hm := mul_le_mul_of_nonneg_left hbound (by linarith : 0 ≤ 3 * s)
  apply (div_le_div_iff₀ (by linarith : 0 < 2 * s + 3) hroot).2
  nlinarith only [hm]
