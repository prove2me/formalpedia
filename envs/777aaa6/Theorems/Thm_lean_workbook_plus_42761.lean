-- Prove2me | Theorems.Thm_lean_workbook_plus_42761
-- name    : lean_workbook_plus_42761
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/44fdc831-e49d-4e8f-a0ec-8bb3e71d7d54
-- statement:
--   Let $0\leq a,b,c\leq \frac{1}{2}$ such that $a+b+c=3$, prove that $a^3+b^3+c^3+4abc\leq \frac{9}{32}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42761 (a b c : ℝ) (ha : 0 ≤ a ∧ a ≤ 1 / 2) (hb : 0 ≤ b ∧ b ≤ 1 / 2) (hc : 0 ≤ c ∧ c ≤ 1 / 2) (habc : a + b + c = 3) : a^3 + b^3 + c^3 + 4 * a * b * c ≤ 9 / 32   :=  by sorry
