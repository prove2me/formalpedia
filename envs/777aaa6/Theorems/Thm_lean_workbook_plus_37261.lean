-- Prove2me | Theorems.Thm_lean_workbook_plus_37261
-- name    : lean_workbook_plus_37261
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3ab1f7a1-58c1-4300-989f-bd951c2dfb5e
-- statement:
--   The sum of four real numbers is $9$ and the sum of their squares is $21$ . Prove that these numbers can be denoted by $a, b, c, d$ so that $ab-cd \ge 2$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37261 (a b c d : ℝ) (h₁ : a + b + c + d = 9) (h₂ : a^2 + b^2 + c^2 + d^2 = 21) : ∃ a b c d : ℝ, a + b + c + d = 9 ∧ a^2 + b^2 + c^2 + d^2 = 21 ∧ a * b - c * d ≥ 2   :=  by sorry
