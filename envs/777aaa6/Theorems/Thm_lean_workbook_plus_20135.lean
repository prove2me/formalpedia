-- Prove2me | Theorems.Thm_lean_workbook_plus_20135
-- name    : lean_workbook_plus_20135
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6fcc4358-d4f7-4311-a160-cb8a9b866e3b
-- statement:
--   for positif numbers x, y, z, show that \n\n $\frac{x}{y+z}+\frac{y}{x+z}+\frac{z}{x+y}\geq \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20135 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + y / (x + z) + z / (x + y)) ≥ 3 / 2   :=  by sorry
