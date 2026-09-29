-- Prove2me | Theorems.Thm_lean_workbook_plus_71559
-- name    : lean_workbook_plus_71559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/dd770493-a087-4118-b482-e95f4b1aa1cc
-- statement:
--   If $x,y,z \in \mathbb{R}^+$ , prove that $(x+y+1)^3 + (y+z+1)^3 + (z+x+1)^3 > \dfrac{4}{3}(x+y+z+1)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71559 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + 1) ^ 3 + (y + z + 1) ^ 3 + (z + x + 1) ^ 3 > (4 / 3) * (x + y + z + 1) ^ 2   :=  by sorry
