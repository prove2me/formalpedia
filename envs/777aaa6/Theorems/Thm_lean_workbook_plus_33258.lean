-- Prove2me | Theorems.Thm_lean_workbook_plus_33258
-- name    : lean_workbook_plus_33258
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/d7b31fd8-8e13-4c32-a3ed-6f12373f10f2
-- statement:
--   Let $x,y>0$ and $ \frac{1}{x + 2} + \frac{2}{y + 2} = \frac{1}{3}.$ Prove that $$x+2y\geq 21$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33258 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 1/(x + 2) + 2/(y + 2) = 1/3) : x + 2*y ≥ 21   :=  by sorry
