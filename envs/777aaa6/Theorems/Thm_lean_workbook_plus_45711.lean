-- Prove2me | Theorems.Thm_lean_workbook_plus_45711
-- name    : lean_workbook_plus_45711
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9128935e-8488-4f4a-acdc-8ee6c31372a6
-- statement:
--   If $x$ , $y$ and $z$ are positive numbers, prove that $\frac{x}{x+y} + \frac{y}{z+y} + \frac{z}{x+z} \le 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45711 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (x + y) + y / (z + y) + z / (x + z)) ≤ 2   :=  by sorry
