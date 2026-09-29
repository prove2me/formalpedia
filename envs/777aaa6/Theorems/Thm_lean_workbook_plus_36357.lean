-- Prove2me | Theorems.Thm_lean_workbook_plus_36357
-- name    : lean_workbook_plus_36357
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/382a6658-3728-4adc-b976-93c0f1fce2c1
-- statement:
--   $z=a+bi$ ; $b\neq 0; a^2+b^2=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36357 (a b : ℝ) (h₁ : b ≠ 0) (h₂ : a^2 + b^2 = 1) : ∃ z : ℂ, z = a + b * I ∧ b ≠ 0 ∧ a^2 + b^2 = 1   :=  by sorry
