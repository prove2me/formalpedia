-- Prove2me | Theorems.Thm_lean_workbook_plus_75839
-- name    : lean_workbook_plus_75839
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/26d34888-1da2-4f43-9bbd-d407b98d526e
-- statement:
--   Let $x,y\geq 0$ and $x+y^3=y^4+1.$ Prove that $y+x^3\leq x^4+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75839 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y^3 = y^4 + 1) : y + x^3 ≤ x^4 + 1   :=  by sorry
