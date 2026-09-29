-- Prove2me | solution 1 for lean_workbook_plus_3586
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:31:59.724578+00:00
-- url     : https://prove2.me/submissions/eab21d35-b5a6-427a-a412-fac73d456b51

import Theorems.Thm_lean_workbook_plus_3586
import Mathlib.Tactic.Linarith

theorem solution (x a : ℝ) : (3 - x) ^ 2 ≥ 4 * (x ^ 2 - 3 * x + a) ↔ (x - 1) ^ 2 ≤ 4 - 4 * a / 3 := by
  constructor <;> intro h <;> nlinarith [h]
