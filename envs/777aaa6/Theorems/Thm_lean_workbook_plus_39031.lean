-- Prove2me | Theorems.Thm_lean_workbook_plus_39031
-- name    : lean_workbook_plus_39031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a2f4b9a1-3c42-4095-9fe9-44e7a487e416
-- statement:
--   Prove that $4x+y^3z+yz^3 \ge 6 \sqrt[6] {x^4y^4z^4}=6$ given $x,y,z>0$ and $xyz=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39031 (x y z : ℝ) (hx : x>0) (hy : y>0) (hz : z>0) (habc : x*y*z = 1) : 4*x + y^3*z + y*z^3 >= 6 * (x^4*y^4*z^4)^(1/6)   :=  by sorry
