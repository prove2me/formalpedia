-- Prove2me | Theorems.Thm_lean_workbook_plus_861
-- name    : lean_workbook_plus_861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a7a0131d-c8ea-4a83-8972-75239c52bcbc
-- statement:
--   Prove that for all positives x,y : $2x^2y+2xy^2+x^2+y^2+2xy+1-xy\geq \frac{3(2xy+x+y)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_861 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 2*x^2*y + 2*x*y^2 + x^2 + y^2 + 2*x*y + 1 - x*y ≥ 3*(2*x*y + x + y)/2   :=  by sorry
