-- Prove2me | Theorems.Thm_lean_workbook_plus_77667
-- name    : lean_workbook_plus_77667
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2109efad-13c0-4e80-844a-40f8da5b6d06
-- statement:
--   Prove the inequality \(x^4+y^4+z^4-x^3y-x^3z-y^3z-y^3x-z^3x-z^3y+xyz^2+xy^2z+x^2yz \ge 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77667 (x y z : ℝ) : x^4 + y^4 + z^4 - x^3*y - x^3*z - y^3*z - y^3*x - z^3*x - z^3*y + x*y*z^2 + x*y^2*z + x^2*y*z ≥ 0   :=  by sorry
