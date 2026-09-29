-- Prove2me | Theorems.Thm_lean_workbook_plus_65620
-- name    : lean_workbook_plus_65620
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/07cfff70-cef6-4269-9769-b8a5dca7c4ff
-- statement:
--   Let x= a+b+c. Show that $(a+b+c)^2+(3-a-b-c)^2= 2(x-3/2)^2+9/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65620 (x a b c : ℝ) (h : x = a + b + c) : (a + b + c) ^ 2 + (3 - a - b - c) ^ 2 = 2 * (x - 3 / 2) ^ 2 + 9 / 2   :=  by sorry
