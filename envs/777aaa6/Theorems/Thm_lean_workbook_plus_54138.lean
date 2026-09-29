-- Prove2me | Theorems.Thm_lean_workbook_plus_54138
-- name    : lean_workbook_plus_54138
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/a1433e7e-2c7a-43b4-8dfc-d3c6e544c805
-- statement:
--   Let be a,b and c non-negative reals numbers. Show that\n\n$\frac{b+c}{a^{2}}+\frac{a+c}{b^{2}}+\frac{a+b}{c^{2}}\geq2(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54138 : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (b + c) / a ^ 2 + (a + c) / b ^ 2 + (a + b) / c ^ 2 ≥ 2 * (1 / a + 1 / b + 1 / c)   :=  by sorry
