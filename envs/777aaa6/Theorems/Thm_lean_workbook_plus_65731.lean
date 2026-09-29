-- Prove2me | Theorems.Thm_lean_workbook_plus_65731
-- name    : lean_workbook_plus_65731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/cb69db05-0077-4bfb-b434-9b79fce1487e
-- statement:
--   Let $a,b>0 $ and $ \frac{ a^3}{b}+\frac{ 2b }{a}=3 .$ Prove that\n\n $$a^2+ab+b^2\leq 3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65731 : ∀ a b : ℝ, a > 0 ∧ b > 0 ∧ a^3 / b + 2 * b / a = 3 → a^2 + a * b + b^2 ≤ 3   :=  by sorry
