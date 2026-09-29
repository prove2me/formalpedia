-- Prove2me | Theorems.Thm_lean_workbook_plus_78817
-- name    : lean_workbook_plus_78817
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f9d9813b-fa63-4832-944b-a493a8b6fdda
-- statement:
--   Let $ x,y,z>0, $ with $ xyz=1 $ . Find the minimum value of $ \frac{x}{y+z}+\frac{y}{x+z}+\frac{z}{x+y}. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78817 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : 3 / 2 ≤ x / (y + z) + y / (x + z) + z / (x + y)   :=  by sorry
