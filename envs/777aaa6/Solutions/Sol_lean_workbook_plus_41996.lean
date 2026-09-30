-- Prove2me | solution 1 for lean_workbook_plus_41996
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:12:25.315065+00:00
-- url     : https://prove2.me/submissions/08f29c09-3c47-4d89-8e18-34042a70183d

import Mathlib.Analysis.Complex.Basic

theorem solution    (a d c : ℝ) (hc : 0 < c) (ha : 0 < a ∧ a < c) (hd : 0 < d ∧ d < c)
    (had : a * d < c^2) :
  0 < (a + d) / (1 + a * d / c^2) ∧ (a + d) / (1 + a * d / c^2) < c := by
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨hd0, hdc⟩ := hd
  have hpos : 0 < 1 + a * d / c ^ 2 := by positivity
  constructor
  · positivity
  · rw [div_lt_iff₀ hpos]
    have hc2 : c ^ 2 ≠ 0 := by positivity
    have : c * (1 + a * d / c ^ 2) = c + a * d / c := by
      field_simp
    rw [this]
    have key : a + d < c + a * d / c := by
      rw [← sub_pos]
      have : c + a * d / c - (a + d) = (c - a) * (c - d) / c := by
        field_simp
        ring
      rw [this]
      apply div_pos
      · exact mul_pos (by linarith) (by linarith)
      · exact hc
    exact key
