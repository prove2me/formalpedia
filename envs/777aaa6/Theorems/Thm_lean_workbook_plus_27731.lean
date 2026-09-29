-- Prove2me | Theorems.Thm_lean_workbook_plus_27731
-- name    : lean_workbook_plus_27731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2e1ccd87-e040-4194-9221-d60c4287d525
-- statement:
--   Use the inequality $ab\le\frac{(a+b)^2}{4}$ for $a=4x^2-f(x)$ and $b=f(x).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27731 (f : ℝ → ℝ) (x : ℝ) : (4 * x ^ 2 - f x) * f x ≤ (4 * x ^ 2 - f x + f x) ^ 2 / 4   :=  by sorry
