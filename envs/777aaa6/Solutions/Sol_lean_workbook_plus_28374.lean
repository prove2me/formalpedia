-- Prove2me | solution 1 for lean_workbook_plus_28374
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:34.13856+00:00
-- url     : https://prove2.me/submissions/74b3c8cc-a5f6-456a-88b2-96bca2538945

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ x : ℕ → ℝ, ∀ n, (x (2 * n) = -1 / n ∧ x (2 * n + 1) = 1) := by
  refine ⟨fun k => if k % 2 = 0 then -1 / ((k / 2 : ℕ) : ℝ) else 1, fun n => ?_⟩
  constructor
  · have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]
  · have h1 : (2 * n + 1) % 2 = 1 := by omega
    simp [h1]
