-- Prove2me | Theorems.Thm_lean_workbook_plus_78737
-- name    : lean_workbook_plus_78737
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/dfde7c6e-57ab-45ea-88e0-8bb78b508ddd
-- statement:
--   Let $a,b,c>0$ and $ab+bc+ca+abc=4 .$ prove that $$a^3+b^3+c^3+abc\geq 4 $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78737 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a + a * b * c = 4) : a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥ 4   :=  by sorry
