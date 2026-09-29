-- Prove2me | solution 1 for lean_workbook_plus_22219
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:31:57.39121+00:00
-- url     : https://prove2.me/submissions/d21d3b4c-06ae-4fd8-bfb9-2ae1568206dc

import Theorems.Thm_lean_workbook_plus_22219
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) :
    (a + b + c) ^ 2 = 3 * (a * b + b * c + c * a) ↔
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
  constructor
  · intro h; linear_combination 2 * h
  · intro h; linear_combination h / 2
