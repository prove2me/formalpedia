-- Prove2me | Theorems.Thm_lean_workbook_plus_57953
-- name    : lean_workbook_plus_57953
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/833be687-407c-44dc-83b7-543eea24cdb5
-- statement:
--   Prove that $(x+y+z)^2 \geq 3(xy+yz+zx)$ given $x,y,z > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57953 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x)   :=  by sorry
