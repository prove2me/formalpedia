-- Prove2me | Theorems.Thm_lean_workbook_plus_18303
-- name    : lean_workbook_plus_18303
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/71b020e0-4043-4778-83aa-930330b8d1b5
-- statement:
--   Let $a,b,c>0$ and $a+b+c=a^3+b^3+c^3. $ Prove that\n\n $$ abc\leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18303 (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b + c = a^3 + b^3 + c^3) : a * b * c ≤ 1   :=  by sorry
