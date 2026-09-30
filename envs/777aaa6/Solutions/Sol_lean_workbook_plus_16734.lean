-- Prove2me | solution 1 for lean_workbook_plus_16734
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:56:11.261028+00:00
-- url     : https://prove2.me/submissions/c2f19e3e-fdd0-4623-91da-f114d7456b46

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ p q r : ℝ, p = 2 ∧ q = 1 ∧ r ≤ 4 / 27) := by
  intro h
  obtain ⟨hp, _, _⟩ := h 0 0 0
  norm_num at hp
