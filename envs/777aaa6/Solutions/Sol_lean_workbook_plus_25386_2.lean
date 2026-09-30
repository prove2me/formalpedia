-- Prove2me | solution 2 for lean_workbook_plus_25386
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:11.346381+00:00
-- url     : https://prove2.me/submissions/d66268c4-5ee4-43ce-8eb6-ee84a6e485ea

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ a b c : ℝ, a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1 → a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ 1) := by
  intro h
  have := h 1 1 1 ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  norm_num at this
