-- Prove2me | solution 1 for lean_workbook_plus_80978
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:57:02.808347+00:00
-- url     : https://prove2.me/submissions/57b1a949-d908-4aa1-8dd9-458d95f399a6

import Mathlib.Tactic

theorem solution (r a s : ℝ) : r = 1 / 3 * a ∧ a = 1 / 2 * s * Real.sqrt 3 → r = s * Real.sqrt 3 / 6 := by
  rintro ⟨hr, ha⟩; rw [hr, ha]; ring
