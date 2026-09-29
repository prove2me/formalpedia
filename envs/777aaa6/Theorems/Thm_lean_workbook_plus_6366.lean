-- Prove2me | Theorems.Thm_lean_workbook_plus_6366
-- name    : lean_workbook_plus_6366
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3dc1bf7d-4910-42ec-854f-94e348dfd375
-- statement:
--   Prove that if $x,y>0$ then $\frac{x^3+y^3}{x^2+xy+y^2}-\frac{x+y}{3} = \frac{2(x+y)(x-y)^2}{3(x^2+xy+y^2)} \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6366 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^3 + y^3) / (x^2 + x * y + y^2) - (x + y) / 3 = 2 * (x + y) * (x - y)^2 / (3 * (x^2 + x * y + y^2)) ∧ 2 * (x + y) * (x - y)^2 / (3 * (x^2 + x * y + y^2)) >= 0   :=  by sorry
