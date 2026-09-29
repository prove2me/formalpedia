-- Prove2me | Theorems.Thm_lean_workbook_plus_40995
-- name    : lean_workbook_plus_40995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/820b2d59-092a-4f41-b867-18716da2ef69
-- statement:
--   Prove that for all real number $x,y,z$, $(4(x+y+z)-xyz)^2+4(xy+yz+zx-4)^2 \geq 8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40995 (x y z : ℝ) : (4 * (x + y + z) - x * y * z) ^ 2 + 4 * (x * y + y * z + z * x - 4) ^ 2 ≥ 8   :=  by sorry
