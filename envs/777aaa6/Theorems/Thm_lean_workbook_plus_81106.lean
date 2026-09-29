-- Prove2me | Theorems.Thm_lean_workbook_plus_81106
-- name    : lean_workbook_plus_81106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6f6a30c2-3870-49d9-80f3-69332c67c1e7
-- statement:
--   Let $x,y,z\geq 0,$ prove that $|x-y|+|y-z|+|z-x|\geq \frac{1}{2}( |x+y-2z|+|y+z-2x|+|z+x-2y|).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81106 (x y z : ℝ) : |x - y| + |y - z| + |z - x| ≥ 1 / 2 * (|x + y - 2 * z| + |y + z - 2 * x| + |z + x - 2 * y|)   :=  by sorry
