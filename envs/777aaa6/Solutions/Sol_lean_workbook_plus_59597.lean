-- Prove2me | solution 1 for lean_workbook_plus_59597
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:39.59744+00:00
-- url     : https://prove2.me/submissions/90748b7f-0197-45ed-8d89-f093be806571

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) :
    (1 + 1 / a) * (2 + 1 / b) * (3 + 1 / c) ≤ 91 / 8 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have h1 : 1 / a ≤ 1 / 2 := by rw [div_le_div_iff₀ ha0 (by norm_num)]; linarith
  have h2 : 1 / b ≤ 1 / 3 := by rw [div_le_div_iff₀ hb0 (by norm_num)]; linarith
  have h3 : 1 / c ≤ 1 / 4 := by rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
  have p1 : 0 ≤ 1 / a := by positivity
  have p2 : 0 ≤ 1 / b := by positivity
  have p3 : 0 ≤ 1 / c := by positivity
  calc (1 + 1 / a) * (2 + 1 / b) * (3 + 1 / c)
      ≤ (1 + 1 / 2) * (2 + 1 / 3) * (3 + 1 / 4) := by
        apply mul_le_mul
        · apply mul_le_mul <;> linarith
        · linarith
        · linarith
        · positivity
    _ = 91 / 8 := by norm_num
