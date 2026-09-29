-- Prove2me | Theorems.Thm_lean_workbook_plus_74609
-- name    : lean_workbook_plus_74609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ceda77d0-e195-4d5b-a6e0-17135ad063da
-- statement:
--   Prove that for all $x,y,z,t > 0$ we have that $ \frac{x}{x+y+z+t} + \frac{x+y}{x+y+z} > 2 \cdot \frac{2x+y}{2x+2y+2z+t} \, . $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74609 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : (x / (x + y + z + t) + (x + y) / (x + y + z)) > 2 * (2 * x + y) / (2 * x + 2 * y + 2 * z + t)   :=  by sorry
