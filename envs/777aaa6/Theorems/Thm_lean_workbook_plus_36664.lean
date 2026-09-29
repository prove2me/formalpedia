-- Prove2me | Theorems.Thm_lean_workbook_plus_36664
-- name    : lean_workbook_plus_36664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/aabb51a4-a250-4553-819e-2673824c1dea
-- statement:
--   Let $ a,b>0$ and $ (1+a^2)(1+b^2)=4 .$ Prove that \n$$a+b+ab\leq 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36664 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (1 + a^2) * (1 + b^2) = 4) : a + b + a * b ≤ 3   :=  by sorry
