-- Prove2me | Theorems.Thm_lean_workbook_plus_23029
-- name    : lean_workbook_plus_23029
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2fe6fdd7-a1b5-4bf8-b363-e20ea577d58f
-- statement:
--   Show that $\left(x+\frac{1}{x}\right)\left(\left(x+\frac{1}{x}\right)^2-3\right)=x^3+\frac{1}{x^3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23029 (x : ℝ) (hx : x ≠ 0) : (x + 1/x) * ((x + 1/x)^2 - 3) = x^3 + 1/(x^3)   :=  by sorry
