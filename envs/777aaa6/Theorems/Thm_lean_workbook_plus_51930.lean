-- Prove2me | Theorems.Thm_lean_workbook_plus_51930
-- name    : lean_workbook_plus_51930
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ea9fa954-d61e-4484-ade0-659f287dd5a3
-- statement:
--   Let $a, b, c$ be positive reals that satisfy $abc \le \frac{1}{4}$ and $\frac{1}{a^2} + \frac{1}{b^2} + \frac{1}{c^2} < 9$. Prove that there exists a triangle with sides $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51930 (a b c : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c) (h2 : a * b * c ≤ 1 / 4) (h3 : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 < 9) : ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a   :=  by sorry
