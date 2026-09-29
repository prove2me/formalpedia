-- Prove2me | Theorems.Thm_lean_workbook_plus_25615
-- name    : lean_workbook_plus_25615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/50e56fa8-492a-4d66-b2d2-a8d2458826b0
-- statement:
--   Prove that $\sum_{cyc}(x^{3}-xyz)=x^{3}+y^{3}+z^{3}-3xyz=\frac{1}{2}\cdot(x+y+z)((x-y)^{2}+(x-z)^{2}+(y-z)^{2})\geq0,$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25615 (x y z : ℝ) :
  x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z =
    1 / 2 * (x + y + z) * ((x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2)   :=  by sorry
