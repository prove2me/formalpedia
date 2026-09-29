-- Prove2me | Theorems.Thm_lean_workbook_plus_1110
-- name    : lean_workbook_plus_1110
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/71269c86-cac4-4497-95e6-46d073507622
-- statement:
--   Prove that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a}\geq a^2+b^2+c^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1110 : ∀ a b c : ℝ, (a / b + b / c + c / a) ≥ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
