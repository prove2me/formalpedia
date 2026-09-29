-- Prove2me | Theorems.Thm_lean_workbook_plus_194
-- name    : lean_workbook_plus_194
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ff1018c9-ac85-40f4-8d89-533ad5ba4214
-- statement:
--   The area of the rectangle is $2x(9-x^2)$, where x is positive, since the dimensions are $2x$ in width and $9-x^2$ in height. We are given that it is equal to 20. Therefore, $x(9-x^2)=10$, and $x^3-9x+10=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_194 (x : ℝ) (hx : x > 0) (h : x * (9 - x^2) = 10) : x^3 - 9 * x + 10 = 0   :=  by sorry
