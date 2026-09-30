-- Prove2me | solution 1 for lean_workbook_plus_62107
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:58.962387+00:00
-- url     : https://prove2.me/submissions/727a5e9b-5a2d-4e5d-8b2e-dfe8d822dd95

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : ⌊n + Real.sqrt n + 1 / 2⌋ = n + ⌊Real.sqrt n + 1 / 2⌋ := by
  rw [add_assoc, Int.floor_natCast_add]
