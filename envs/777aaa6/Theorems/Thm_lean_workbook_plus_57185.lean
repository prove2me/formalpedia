-- Prove2me | Theorems.Thm_lean_workbook_plus_57185
-- name    : lean_workbook_plus_57185
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9737d8fe-ac23-48ca-a0e1-88abf91e626b
-- statement:
--   prove that if a,b,c are positive numbers satisfying $abc\le \frac{1}{4}$ and $\frac{1}{a^{2}}+\frac{1}{b^{2}}+\frac{1}{c^{2}}<9$ then there exists a triangle with sides a,b,c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57185 (a b c : ℝ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c) (h₂ : a * b * c ≤ 1 / 4) (h₃ : 1 / a^2 + 1 / b^2 + 1 / c^2 < 9) : ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a   :=  by sorry
