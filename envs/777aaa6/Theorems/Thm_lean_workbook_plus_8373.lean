-- Prove2me | Theorems.Thm_lean_workbook_plus_8373
-- name    : lean_workbook_plus_8373
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e64300f0-f785-48a6-bd0f-254e37c0fd76
-- statement:
--   For $n=5$ then ineq is equivalent to $$\left(x_1-\dfrac{1}{2}x_5\right)^2+\left(x_2-\dfrac{1}{2}x_5\right)^2+\left(x_3-\dfrac{1}{2}x_5\right)^2+\left(x_4-\dfrac{1}{2}x_5\right)^2\ge 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8373 (x : ℕ → ℝ) : (x 1 - 1 / 2 * x 5) ^ 2 + (x 2 - 1 / 2 * x 5) ^ 2 + (x 3 - 1 / 2 * x 5) ^ 2 + (x 4 - 1 / 2 * x 5) ^ 2 ≥ 0   :=  by sorry
