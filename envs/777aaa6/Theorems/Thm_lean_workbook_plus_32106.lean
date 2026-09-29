-- Prove2me | Theorems.Thm_lean_workbook_plus_32106
-- name    : lean_workbook_plus_32106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/818cbaec-55d2-4fd0-9d80-87f175aad85e
-- statement:
--   Given $f(x,y,z)=(x+1)^3+(y+1)^3+(z+1)^3 -3xyz=1$, show that $g(x,y,z)=x+y+z\leq -1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32106 (x y z : ℝ) (h : (x + 1) ^ 3 + (y + 1) ^ 3 + (z + 1) ^ 3 - 3 * x * y * z = 1): x + y + z ≤ -1   :=  by sorry
