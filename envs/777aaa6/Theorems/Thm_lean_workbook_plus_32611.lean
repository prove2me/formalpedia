-- Prove2me | Theorems.Thm_lean_workbook_plus_32611
-- name    : lean_workbook_plus_32611
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/34c3a20a-25b0-4458-82e4-d7a22aceb8b0
-- statement:
--   Prove that $x^2\left(x-y\right)\left(x-z\right)+y^2\left(y-z\right)\left(y-x\right)+z^2\left(z-x\right)\left(z-y\right)$\n\n$=\frac12\left(\left(y+z-x\right)^2\left(y-z\right)^2+\left(z+x-y\right)^2\left(z-x\right)^2+\left(x+y-z\right)^2\left(x-y\right)^2\right)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32611 (x y z : ℝ) : x ^ 2 * (x - y) * (x - z) + y ^ 2 * (y - z) * (y - x) + z ^ 2 * (z - x) * (z - y) = 1 / 2 * ((y + z - x) ^ 2 * (y - z) ^ 2 + (z + x - y) ^ 2 * (z - x) ^ 2 + (x + y - z) ^ 2 * (x - y) ^ 2)   :=  by sorry
