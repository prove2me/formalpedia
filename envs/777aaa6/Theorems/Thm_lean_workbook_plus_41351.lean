-- Prove2me | Theorems.Thm_lean_workbook_plus_41351
-- name    : lean_workbook_plus_41351
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0dec145d-912c-4670-8ca8-82294c423514
-- statement:
--   Let $a, b, c$ be positive real numbers. Prove that the following inequality is true: \n\n $\dfrac{a}{b+c}+\dfrac{b}{a+c}+\dfrac{c}{a+b}\ge\dfrac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41351 : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 → a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2)   :=  by sorry
