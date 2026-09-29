-- Prove2me | Theorems.Thm_lean_workbook_plus_19462
-- name    : lean_workbook_plus_19462
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cc54de8c-c7bc-4eef-8a86-caabb0633421
-- statement:
--   For $ a, b, c $ non-negative numbers prove that:\n\n $ (a^2+ab+b^2)(b^2+bc+c^2)(c^2+ca+a^2) \ge \n\n \frac{1}{3} \cdot (ab+bc+ca)^2 \cdot (2a^2+2b^2+2c^2+ab+bc+ca) \ \ ; $\n\nThis in an improvement of Cirtoaje-Lascu inequality, from `Algebraic Inequalities` page 9, problem 34.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19462 : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ 1 / 3 * (a * b + b * c + c * a)^2 * (2 * a^2 + 2 * b^2 + 2 * c^2 + a * b + b * c + c * a)   :=  by sorry
