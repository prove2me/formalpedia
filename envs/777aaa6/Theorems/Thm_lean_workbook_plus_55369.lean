-- Prove2me | Theorems.Thm_lean_workbook_plus_55369
-- name    : lean_workbook_plus_55369
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/da14a049-13b2-483a-a270-ff49a8eda37d
-- statement:
--   Find the value of $16x_1+25x_2+36x_3+49x_4+64x_5+81x_6+100x_7$ given the following system of equations:\n$x_1+4x_2+9x_3+16x_4+25x_5+36x_6+49x_7=1$\n$4x_1+9x_2+16x_3+25x_4+36x_5+49x_6+64x_7=12$\n$9x_1+16x_2+25x_3+36x_4+49x_5+64x_6+81x_7=123$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55369 (x : ℕ → ℝ) : x 1 + 4 * x 2 + 9 * x 3 + 16 * x 4 + 25 * x 5 + 36 * x 6 + 49 * x 7 = 1 ∧ 4 * x 1 + 9 * x 2 + 16 * x 3 + 25 * x 4 + 36 * x 5 + 49 * x 6 + 64 * x 7 = 12 ∧ 9 * x 1 + 16 * x 2 + 25 * x 3 + 36 * x 4 + 49 * x 5 + 64 * x 6 + 81 * x 7 = 123 → 16 * x 1 + 25 * x 2 + 36 * x 3 + 49 * x 4 + 64 * x 5 + 81 * x 6 + 100 * x 7 = 334   :=  by sorry
