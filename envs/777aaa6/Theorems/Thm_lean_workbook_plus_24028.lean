-- Prove2me | Theorems.Thm_lean_workbook_plus_24028
-- name    : lean_workbook_plus_24028
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/83946c16-5470-4341-9970-9eed92512daf
-- statement:
--   Let $ x,y,z$ be positive numbers satisfying $ x(x + y + z) = 3yz$ .Prove that \n $ (x + y)^3 + (x + z)^3 + 3(x + y)(y + z)(z + x)\le 5(y + z)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24028 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * (x + y + z) = 3 * y * z) : (x + y) ^ 3 + (x + z) ^ 3 + 3 * (x + y) * (y + z) * (z + x) ≤ 5 * (y + z) ^ 3   :=  by sorry
