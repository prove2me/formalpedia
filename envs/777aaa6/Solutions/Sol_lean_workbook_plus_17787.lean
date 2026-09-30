-- Prove2me | solution 1 for lean_workbook_plus_17787
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T19:54:56.841415+00:00
-- url     : https://prove2.me/submissions/187374be-c481-4417-9be3-efca0504817d

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (z x : ℝ), 0 < z ∧ 0 < x → z / x = 1.8 / 6.5 → x = 20 → z = 5.5) := by
  intro h
  have := h (72 / 13) 20 ⟨by norm_num, by norm_num⟩ (by norm_num) rfl
  norm_num at this
