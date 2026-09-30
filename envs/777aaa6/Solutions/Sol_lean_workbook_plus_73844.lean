-- Prove2me | solution 1 for lean_workbook_plus_73844
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:19.728802+00:00
-- url     : https://prove2.me/submissions/ed6ad17b-5b7f-42e0-a8f7-e6597890f4bf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ 2 - a * b + b ^ 2) * (a + b) ^ 4 ≥ 16 * a ^ 3 * b ^ 3 := by
  have hid : (a ^ 2 - a * b + b ^ 2) * (a + b) ^ 4 - 16 * a ^ 3 * b ^ 3 =
      (a - b) ^ 2 * ((a - b) ^ 4 + 9 * a * b * (a - b) ^ 2 +
        24 * a ^ 2 * b ^ 2) := by ring
  have hn : 0 ≤ (a - b) ^ 2 * ((a - b) ^ 4 + 9 * a * b * (a - b) ^ 2 +
      24 * a ^ 2 * b ^ 2) := by positivity
  linarith

#print axioms solution
