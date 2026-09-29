-- Prove2me | Theorems.Thm_lean_workbook_plus_40699
-- name    : lean_workbook_plus_40699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1cc5b1da-a47a-4646-ac6c-41e54d0ff7c2
-- statement:
--   Let $a\geq b\geq c>0.$ Prove that $$(a-b+c) \left(\frac{1}{a}-\frac{1}{b}+\frac{1}{c}\right)\geq 1.$$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40699 (a b c : ℝ) (h₁ : a ≥ b ∧ b ≥ c ∧ c > 0) : (a - b + c) * (1 / a - 1 / b + 1 / c) ≥ 1   :=  by sorry
