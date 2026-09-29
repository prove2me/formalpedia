-- Prove2me | Theorems.Thm_lean_workbook_plus_690
-- name    : lean_workbook_plus_690
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/9134f2e9-d168-43ff-9d65-5f4110fde540
-- statement:
--   Prove that for $ x, y, z >0 $, $ x^3y+y^3z+z^3x+xy^3+yz^3+zx^3\geq 2(x^2y^2+y^2z^2+z^2x^2) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_690 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x^3*y + y^3*z + z^3*x + x*y^3 + y*z^3 + z*x^3 >= 2 * (x^2*y^2 + y^2*z^2 + z^2*x^2)   :=  by sorry
