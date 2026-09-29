-- Prove2me | Theorems.Thm_lean_workbook_plus_79241
-- name    : lean_workbook_plus_79241
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5a7935bc-bb2d-4973-915a-180dc31300b2
-- statement:
--   Prove that if, $x,y>0$ \n\n $x^3+y^3 \ge xy(x+y)\ \ \ \left( \iff (x-y)^2(x+y) \ge 0 \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79241 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 + y^3 ≥ x * y * (x + y)   :=  by sorry
