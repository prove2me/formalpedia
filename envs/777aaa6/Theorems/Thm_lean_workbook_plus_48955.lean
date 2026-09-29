-- Prove2me | Theorems.Thm_lean_workbook_plus_48955
-- name    : lean_workbook_plus_48955
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d1bc13ff-f4f4-48fc-86f9-1f5558c9a0a0
-- statement:
--   Substitute $x_5=1-x_1-x_2-x_3-x_4$ into $x_1^2+x_2^2+x_3^2+x_4^2+x_5^2\le 1/4$ to get a quadratic in $x_1$ : $f(x_1)= x_1^2-x_1(1-x_2-x_3-x_4)+x_2^2+x_3^2+x_4^2-x_2-x_3-x_4+x_2x_3+x_2x_4+x_3x_4+3/8\le 0.\ \ (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48955 : ∀ x : ℝ, ∀ x_1 : ℝ, ∀ x_2 : ℝ, ∀ x_3 : ℝ, ∀ x_4 : ℝ, x_1 + x_2 + x_3 + x_4 + (1 - x_1 - x_2 - x_3 - x_4) = 1 ∧ x_1^2 + x_2^2 + x_3^2 + x_4^2 + (1 - x_1 - x_2 - x_3 - x_4)^2 ≤ 1 / 4 → x_1^2 - x_1 * (1 - x_2 - x_3 - x_4) + x_2^2 + x_3^2 + x_4^2 - x_2 - x_3 - x_4 + x_2 * x_3 + x_2 * x_4 + x_3 * x_4 + 3 / 8 ≤ 0   :=  by sorry
