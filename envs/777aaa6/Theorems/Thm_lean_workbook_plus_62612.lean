-- Prove2me | Theorems.Thm_lean_workbook_plus_62612
-- name    : lean_workbook_plus_62612
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c8d56b14-6d27-46d3-b2a6-4245f60ce69f
-- statement:
--   Prove that $x^3y+y^3z+z^3x=-9$ given $x+y+z=0$ and $x^2+y^2+z^2=6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62612 (x y z : ℝ) (hx : x + y + z = 0) (hy : x ^ 2 + y ^ 2 + z ^ 2 = 6) : x ^ 3 * y + y ^ 3 * z + z ^ 3 * x = -9   :=  by sorry
