-- Prove2me | Theorems.Thm_lean_workbook_plus_80144
-- name    : lean_workbook_plus_80144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/937d55ea-6e56-4e1d-bfea-36582a1ac660
-- statement:
--   Prove that $ \ \frac{1}{x+y} + \frac{1}{y+z} + \frac{1}{z+x} > \frac{3}{x+y+z}$ , for all positive numbers $ x, y$ and $ z$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80144 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) > 3 / (x + y + z)   :=  by sorry
