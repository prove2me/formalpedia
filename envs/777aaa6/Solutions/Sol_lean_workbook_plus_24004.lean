-- Prove2me | solution 1 for lean_workbook_plus_24004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:10.241705+00:00
-- url     : https://prove2.me/submissions/cb3ed889-72d3-4908-95df-209f37632bec

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x ∈ Set.Icc 0 1 ∧ f 0 = 0 ∧ f 1 = 1 := by
  refine ⟨fun x => max 0 (min 1 x), fun x => ⟨⟨le_max_left _ _, ?_⟩, ?_, ?_⟩⟩
  · exact max_le zero_le_one (min_le_left _ _)
  · simp
  · simp
