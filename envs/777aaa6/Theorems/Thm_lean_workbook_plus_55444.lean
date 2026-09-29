-- Prove2me | Theorems.Thm_lean_workbook_plus_55444
-- name    : lean_workbook_plus_55444
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bb962b73-0b70-48df-ad68-fd6f6db5fcd1
-- statement:
--   Show that $\sum {x\left( {1 - y^2 - z^2 + y^2 z^2 } \right)} = \sum x + xyz - \sum {xy\left( {x + y} \right)} = 4xyz$ given $x,y,z\geq 0$ and $xy + xz + yz = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55444 {x y z : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x * y + x * z + y * z = 1) : x * (1 - y ^ 2 - z ^ 2 + y ^ 2 * z ^ 2) + y * (1 - z ^ 2 - x ^ 2 + z ^ 2 * x ^ 2) + z * (1 - x ^ 2 - y ^ 2 + x ^ 2 * y ^ 2) = 4 * x * y * z   :=  by sorry
