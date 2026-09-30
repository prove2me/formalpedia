-- Prove2me | solution 1 for lean_workbook_plus_14608
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:17:49.390401+00:00
-- url     : https://prove2.me/submissions/f97f58d1-90f8-4e6f-941c-bdf3dcabfac3

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ n : ℕ, ∃ a b c : ℕ, a^2 + b^2 = c^2 := by
  intro _
  exact ⟨3, 4, 5, by norm_num⟩
