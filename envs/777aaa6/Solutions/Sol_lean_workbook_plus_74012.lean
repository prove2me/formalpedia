-- Prove2me | solution 1 for lean_workbook_plus_74012
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:32:00.858132+00:00
-- url     : https://prove2.me/submissions/209a9663-6fed-4f5f-8437-63705fd5caff

import Theorems.Thm_lean_workbook_plus_74012
import Mathlib.Tactic.Ring

theorem solution : ∀ a b c : ℝ, (3 * a + 4 * b + 5 * c) ^ 2 - 44 * (a * b + b * c + c * a) = (b - 2 * c) ^ 2 + 7 / 3 * (a - 3 * c) ^ 2 + 5 / 3 * (2 * a - 3 * b) ^ 2 := by
  intro a b c; ring
