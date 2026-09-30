-- Prove2me | solution 1 for lean_workbook_plus_76298
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:39.480314+00:00
-- url     : https://prove2.me/submissions/f63e567c-3886-4bb8-9e26-c368d41c5df8

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c : ℝ} (h : a + b * c = b + c * a ∧ b + c * a = c + a * b) : (a - b) * (c - 1) = 0 ∧ (b - c) * (a - 1) = 0 ∧ (c - a) * (b - 1) = 0 := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -h1
  · linear_combination -h2
  · linear_combination h1 + h2
