-- Prove2me | solution 1 for lean_workbook_plus_7170
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:44:05.670059+00:00
-- url     : https://prove2.me/submissions/7f33efad-0f0c-41e8-89b6-32a188860317

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 / (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1))) ≥ 1 + (3 / (1 / a + 1 / b + 1 / c)) ↔ (1 / (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1))) - (1 / (1 / a + 1 / b + 1 / c)) ≥ 1 / 3 := by
  have e : ∀ s : ℝ, 3 / s = 3 * (1 / s) := fun s => by ring
  rw [e, e]
  constructor <;> intro h <;> linarith
