-- Prove2me | Theorems.Thm_lean_workbook_plus_8313
-- name    : lean_workbook_plus_8313
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/2ae20a67-70fc-4d03-a5ae-60b9dc4f742e
-- statement:
--   Prove that for positive real numbers $x, y, z$ satisfying $xyz = 1$, the following inequality holds:\n$(\sum_{sym}x^{5}y+\sum_{cyc}x^{4}yz)\leq 3\sum_{cyc}x^{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8313 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : (x ^ 5 * y + y ^ 5 * z + z ^ 5 * x + (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y)) ≤ 3 * (x ^ 6 + y ^ 6 + z ^ 6)   :=  by sorry
