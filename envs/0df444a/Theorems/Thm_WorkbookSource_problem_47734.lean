-- Prove2me | Theorems.Thm_WorkbookSource_problem_47734
-- name    : WorkbookSource.problem_47734
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:14:00.062961+00:00
-- url     : https://prove2.me/theorems/2c768135-28f8-4e05-a904-234eb10452ec
-- title:
--   An identity under a positive unit-product constraint
-- statement:
--   Let $x,y,z\in R^+$ such that $ xyz=1$ . Prove that
--
--    $\left(x+\frac{1}{x}-\frac{z}{y}\right)^2+$ $\left(y+\frac{1}{y}-\frac{x}{z}\right)^2+$ $\left(z+\frac{1}{z}-\frac{y}{x}\right)^2+$ $\left(x+\frac{1}{x}-\frac{z}{y}\right) \left(y+\frac{1}{y}-\frac{x}{z}\right) \left(z+\frac{1}{z}-\frac{y}{x}\right)=4$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47734` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47734; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_47734 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : (x + 1 / x - z / y)^2 + (y + 1 / y - x / z)^2 + (z + 1 / z - y / x)^2 + (x + 1 / x - z / y) * (y + 1 / y - x / z) * (z + 1 / z - y / x) = 4  :=  by sorry
