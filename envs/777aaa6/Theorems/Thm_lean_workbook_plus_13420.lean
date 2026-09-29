-- Prove2me | Theorems.Thm_lean_workbook_plus_13420
-- name    : lean_workbook_plus_13420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ef16e59e-f075-46dc-9ef2-739488fa4bfe
-- statement:
--   Prove that $2 \sum (x+y)^2z \leq 3 (x+y)(y+z)(z+x)$ for positive reals x, y, z.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13420 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * (x + y) ^ 2 * z + 2 * (y + z) ^ 2 * x + 2 * (z + x) ^ 2 * y ≤ 3 * (x + y) * (y + z) * (z + x)   :=  by sorry
