-- Prove2me | solution 1 for lean_workbook_plus_71322
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:25:40.300086+00:00
-- url     : https://prove2.me/submissions/9038d3e6-4720-48b9-b6be-d4704503f357

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (a + 2 * b) + 1 / (b + 2 * a) ≤ 2 / (3 * Real.sqrt (a * b)) := by
  have hr : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hr2 : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (mul_pos ha hb).le
  have hs : 2 * Real.sqrt (a * b) ≤ a + b := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg (a - b)]
  have hm : 0 ≤ (a + b - 2 * Real.sqrt (a * b)) *
      (4 * (a + b) - Real.sqrt (a * b)) :=
    mul_nonneg (sub_nonneg.mpr hs) (by linarith)
  have hd1 : 0 < a + 2 * b := by positivity
  have hd2 : 0 < b + 2 * a := by positivity
  have hd : 0 < (a + 2 * b) * (b + 2 * a) := mul_pos hd1 hd2
  have he : 1 / (a + 2 * b) + 1 / (b + 2 * a) =
      3 * (a + b) / ((a + 2 * b) * (b + 2 * a)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2] <;> ring
  rw [he]
  apply (div_le_div_iff₀ hd (by positivity)).2
  nlinarith

#print axioms solution
