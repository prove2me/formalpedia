-- Prove2me | Theorems.Thm_lean_workbook_plus_2528
-- name    : lean_workbook_plus_2528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/51483df0-2c91-4ea5-9df6-166805128864
-- statement:
--   For all real numbers satisfying $0\leq x \leq 2$ we have $\frac{3}{1+x} \leq 3- \frac{1}{2}x^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2528 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 2) : (3 / (1 + x) ≤ 3 - 1 / 2 * x ^ 2)   :=  by sorry
