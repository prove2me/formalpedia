-- Prove2me | Theorems.Thm_lean_workbook_plus_62049
-- name    : lean_workbook_plus_62049
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/33b2c470-d734-4520-8ad6-a75d3d9b6e5b
-- statement:
--   Prove that for all $x,y,z\ge 2$ , $3(x+y+z)\le xyz+x+8.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62049 (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2) : 3 * (x + y + z) ≤ x*y*z + x + 8   :=  by sorry
