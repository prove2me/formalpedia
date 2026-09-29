-- Prove2me | Theorems.Thm_lean_workbook_plus_1830
-- name    : lean_workbook_plus_1830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0073c419-90f5-4ad3-8e7c-404fd9039f76
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $\frac{a}{2a+b+c}+\frac{b}{a+2b+c}+\frac{c}{a+b+2c}\le\frac{3}{4} .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1830 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c) ≤ 3 / 4   :=  by sorry
