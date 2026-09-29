-- Prove2me | Theorems.Thm_lean_workbook_plus_56820
-- name    : lean_workbook_plus_56820
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/5db09f12-a135-41a7-ae0a-613df7378c4f
-- statement:
--   Given $x = 3$, what is the value of the expression $\frac{x^2-6x+5}{x^2+2x+2}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56820 (x : ℝ) (hx : x = 3) : (x^2 - 6*x + 5) / (x^2 + 2*x + 2) = -4/17   :=  by sorry
