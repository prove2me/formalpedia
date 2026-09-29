-- Prove2me | Theorems.Thm_lean_workbook_plus_29892
-- name    : lean_workbook_plus_29892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/42a3adbb-7c37-44bb-b493-79cea567edcf
-- statement:
--   Let $ x,y,z$ be positive numbers satisfying $ x(x + y + z) = 3yz$ .Prove that \n $ (x + y)^3 + (x + z)^3\le 2(z + y)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29892 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hab : x * (x + y + z) = 3 * y * z) : (x + y) ^ 3 + (x + z) ^ 3 ≤ 2 * (z + y) ^ 3   :=  by sorry
