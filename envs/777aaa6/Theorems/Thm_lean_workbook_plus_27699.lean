-- Prove2me | Theorems.Thm_lean_workbook_plus_27699
-- name    : lean_workbook_plus_27699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/90f9327e-e96a-483d-a418-5898982d9944
-- statement:
--   Prove that $\left\|\begin{array}{c}abc\ne 0\\a^2=b(b+c)\\b^2=c(c+a)\end{array}\right\|\ \implies\ \frac 1c=\frac 1a+\frac 1b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27699 (a b c : ℝ) (h₁ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (h₂ : a^2 = b * (b + c)) (h₃ : b^2 = c * (c + a)) : 1 / c = 1 / a + 1 / b   :=  by sorry
