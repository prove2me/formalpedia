-- Prove2me | Theorems.Thm_lean_workbook_plus_77677
-- name    : lean_workbook_plus_77677
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d73fd38c-a03d-4a03-9cba-5934496ed66a
-- statement:
--   $\frac{b}{c^2}+\frac{c}{a^2}+\frac{a}{b^2} \geq \frac{1}{a}+\frac{1}{b}+\frac{1}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77677 : ∀ a b c : ℝ, (a^2 * b * c ≠ 0 ∧ a * b * c ≠ 0) → b / c^2 + c / a^2 + a / b^2 ≥ 1 / a + 1 / b + 1 / c   :=  by sorry
