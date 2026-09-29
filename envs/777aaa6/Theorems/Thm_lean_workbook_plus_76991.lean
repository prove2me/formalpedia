-- Prove2me | Theorems.Thm_lean_workbook_plus_76991
-- name    : lean_workbook_plus_76991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ab31cb8e-6793-4a76-bb0a-602eb653aeb1
-- statement:
--   Prove the identity \(\left(\frac12\cdot\left(x+y+z\right)\right)^2+\left(\frac12\cdot\left(y+z-x\right)\right)^2+\left(\frac12\cdot\left(z+x-y\right)\right)^2+\left(\frac12\cdot\left(x+y-z\right)\right)^2=x^2+y^2+z^2\) for vectors \(x, y, z\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76991 (x y z : ℝ) : (1 / 2 * (x + y + z)) ^ 2 + (1 / 2 * (y + z - x)) ^ 2 + (1 / 2 * (z + x - y)) ^ 2 + (1 / 2 * (x + y - z)) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2   :=  by sorry
