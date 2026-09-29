-- Prove2me | Theorems.Thm_lean_workbook_plus_55720
-- name    : lean_workbook_plus_55720
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/c8ce2b95-2461-49fa-abe9-53da8a057d6d
-- statement:
--   Let $x,y>0$ and $ \frac{1}{x + 2} + \frac{2}{y + 2} = \frac{1}{3}.$ Prove that $$x+2y\geq 21$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55720 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 1 / (x + 2) + 2 / (y + 2) = 1 / 3) : x + 2 * y ≥ 21   :=  by sorry
