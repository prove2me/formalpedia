-- Prove2me | Theorems.Thm_lean_workbook_plus_1434
-- name    : lean_workbook_plus_1434
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ff84e27a-ea68-4118-92f2-d08ec5ba0877
-- statement:
--   Let $a,b,c\ge 0$ and $a^3+b^3+c^3=a+b+c$ . Prove that \n $$a^2+b^2+c^2\leq 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1434 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = a^3 + b^3 + c^3) : a^2 + b^2 + c^2 ≤ 3   :=  by sorry
