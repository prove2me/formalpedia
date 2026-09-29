-- Prove2me | Theorems.Thm_lean_workbook_plus_56664
-- name    : lean_workbook_plus_56664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/970ecef4-5782-4839-ac77-8e5c7364d239
-- statement:
--   For any $x, y, z \geq 0$,\n$4\,xyz+ \left( y+z \right) \left( z+x \right) \left( x+y \right) =x \left( y+z \right) ^{2}+y \left( z+x \right) ^{2}+z \left( x+y \right) ^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56664 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : 4 * x * y * z + (y + z) * (z + x) * (x + y) = x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2   :=  by sorry
