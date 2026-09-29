-- Prove2me | Theorems.Thm_lean_workbook_plus_55368
-- name    : lean_workbook_plus_55368
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bd705a7d-133b-408a-9114-e4de101777d0
-- statement:
--   Solve in $Z$ the system equation: $|x-2015|+y^2-3z=4$ , $|y-2015|+z^2-3x=4$ , $|z-2015|+x^2-3y=4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55368 (x y z: ℤ) (h1 : |x - 2015| + y ^ 2 - 3 * z = 4) (h2 : |y - 2015| + z ^ 2 - 3 * x = 4) (h3 : |z - 2015| + x ^ 2 - 3 * y = 4) : x = 2015 ∧ y = 2015 ∧ z = 2015   :=  by sorry
