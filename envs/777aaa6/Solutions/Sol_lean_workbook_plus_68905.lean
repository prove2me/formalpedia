-- Prove2me | solution 1 for lean_workbook_plus_68905
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:22.562314+00:00
-- url     : https://prove2.me/submissions/2218ca16-42a9-4441-bea6-5758bae4c130

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : a >= b ∧ b >= c ∧ c > 0) :
  a^2 / (b^2 + c^2) >= b^2 / (c^2 + a^2) ∧ b^2 / (c^2 + a^2) >= c^2 / (a^2 + b^2) := by
  obtain ⟨hab, hbc, hc⟩ := h
  have hb : b > 0 := lt_of_lt_of_le hc hbc
  have ha : a > 0 := lt_of_lt_of_le hb hab
  have h1 : b^2 + c^2 > 0 := by positivity
  have h2 : c^2 + a^2 > 0 := by positivity
  have h3 : a^2 + b^2 > 0 := by positivity
  constructor
  · rw [ge_iff_le, div_le_div_iff₀ h2 h1]
    nlinarith [mul_le_mul hab hab hb.le ha.le, mul_le_mul hbc hbc hc.le hb.le, sq_nonneg c, mul_pos ha hb]
  · rw [ge_iff_le, div_le_div_iff₀ h3 h2]
    nlinarith [mul_le_mul hab hab hb.le ha.le, mul_le_mul hbc hbc hc.le hb.le, sq_nonneg a, mul_pos hb hc]
