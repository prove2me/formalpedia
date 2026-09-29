-- Prove2me | Theorems.Thm_lean_workbook_plus_70204
-- name    : lean_workbook_plus_70204
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b4622149-244a-4025-ac36-966554c53fe0
-- statement:
--   For $x,\ y,\ z>0$ , Prove that : \n $\frac{x}{y+z+2x}+\frac{y}{x+z+2y}+\frac{z}{x+y+2z}\le \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70204 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z + 2 * x) + y / (x + z + 2 * y) + z / (x + y + 2 * z)) ≤ 3 / 4   :=  by sorry
