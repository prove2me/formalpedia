-- Prove2me | solution 1 for lean_workbook_plus_15777
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:42.419759+00:00
-- url     : https://prove2.me/submissions/d40ccdfc-4471-4ac4-89d1-87b907275779

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ n : ℕ, n ≡ 0 [ZMOD 3] → ∃ x : ℕ, n = 3 * x := by
  intro n h
  unfold Int.ModEq at h
  exact ⟨n / 3, by omega⟩
