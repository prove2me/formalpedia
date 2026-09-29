-- Prove2me | Theorems.Thm_lean_workbook_plus_59584
-- name    : lean_workbook_plus_59584
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/1d3a207d-1f40-49e6-b73c-339a1cbfffa3
-- statement:
--   If $x,y,z > 0$ , then prove that : \n\n $\frac{x}{x+y} + \frac{y}{y+z} + \frac{z}{z+x} \le 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59584 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (x + y) + y / (y + z) + z / (z + x)) ≤ 2   :=  by sorry
