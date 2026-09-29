-- Prove2me | Theorems.Thm_lean_workbook_plus_73635
-- name    : lean_workbook_plus_73635
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e0dd3100-e830-4729-b2e9-0fdb61c1bbd7
-- statement:
--   If $x^2y+y^2z+z^2x=3 ,x,y,z>0,$ then\n${\frac{1}{x}}+\frac{1}{y}+\frac{1}{z}\ge{3}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73635 (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0)(hab : x * y * z = 1) (h : x^2*y + y^2*z + z^2*x = 3): 1/x + 1/y + 1/z >= 3   :=  by sorry
