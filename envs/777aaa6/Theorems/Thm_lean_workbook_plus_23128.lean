-- Prove2me | Theorems.Thm_lean_workbook_plus_23128
-- name    : lean_workbook_plus_23128
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f402a65b-ba99-431a-88d6-186ae3fb9d5c
-- statement:
--   Prove that \n $\frac{(y+z-x)^2}{(y+z)^2+x^2}+\frac{(z+x-y)^2}{(z+x)^2+y^2}+\frac{(x+y-z)^2}{(x+y)^2+z^2} \leqslant 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23128 : ∀ x y z : ℝ, (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) + (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) ≤ 3   :=  by sorry
