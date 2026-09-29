-- Prove2me | Theorems.Thm_lean_workbook_plus_77706
-- name    : lean_workbook_plus_77706
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/81254586-b442-46f8-a0b3-90063cc34e15
-- statement:
--   If $x,y,z{\ge}0$ , then prove: $(x+2y+z)(y+2z+x)(z+2x+y){\ge}(3x+z)(3y+x)(3z+y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77706 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + 2 * y + z) * (y + 2 * z + x) * (z + 2 * x + y) ≥ (3 * x + z) * (3 * y + x) * (3 * z + y)   :=  by sorry
