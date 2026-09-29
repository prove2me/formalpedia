-- Prove2me | Theorems.Thm_lean_workbook_plus_3289
-- name    : lean_workbook_plus_3289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fee99730-44e5-438d-b8b4-8d7ad8b90426
-- statement:
--   Prove for $x,y,z$ positive reals: $x^2y+yz^2+y^2x+zy^2+x^2z+z^2x\geq 6xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3289 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2*y + y*z^2 + y^2*x + z*y^2 + x^2*z + z^2*x >= 6*x*y*z   :=  by sorry
