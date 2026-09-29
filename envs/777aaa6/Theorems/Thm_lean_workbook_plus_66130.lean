-- Prove2me | Theorems.Thm_lean_workbook_plus_66130
-- name    : lean_workbook_plus_66130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8103b0ae-1f05-4fac-ad1f-a580eeeb0c1c
-- statement:
--   Let $a,b$ be reals. Prove that $$a^2+ab+b^2\geq 3(a+b-1),$$ $$a^2+ab+b^2\geq 3ab(a+b-ab),$$ $$a^2+ab+b^2\leq 3(a^2-a+1)(b^2-b+1).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66130 : ∀ a b : ℝ, a^2 + a * b + b^2 ≥ 3 * (a + b - 1) ∧ a^2 + a * b + b^2 ≥ 3 * a * b * (a + b - a * b) ∧ a^2 + a * b + b^2 ≤ 3 * (a^2 - a + 1) * (b^2 - b + 1)   :=  by sorry
