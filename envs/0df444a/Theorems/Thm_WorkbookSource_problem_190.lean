-- Prove2me | Theorems.Thm_WorkbookSource_problem_190
-- name    : WorkbookSource.problem_190
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:15:20.6965+00:00
-- url     : https://prove2.me/theorems/a9669dc6-d522-450e-ad9a-de51e84bc4d6
-- title:
--   An inequality with two variables in the unit interval
-- statement:
--   For $x,y\in[0,1]$, $x+y\le1$ and $z\ge1$, $$8x^2y^2+z(x+y)^2\ge4xyz.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_190` (Apache-2.0). The complete source proposition is preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_190; Apache-2.0

import Mathlib

theorem WorkbookSource.problem_190 (x y z : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (hxy : x + y ≤ 1) (hz : z ≥ 1) : 8 * x ^ 2 * y ^ 2 + z * (x + y) ^ 2 ≥ 4 * x * y * z  :=  by sorry
