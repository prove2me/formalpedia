-- Prove2me | Theorems.Thm_lean_workbook_plus_36945
-- name    : lean_workbook_plus_36945
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5ed63e8c-69b1-49f9-a719-f36966c33368
-- statement:
--   (Outline) $ \frac{b+c}{a}+\frac{c+a}{b}+\frac{a+b}{c}=0 $ is equivalent to $(a+b+c)(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}) = -3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36945  (a b c : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
  (h₁ : a + b + c ≠ 0)
  (h₂ : (b + c) / a + (c + a) / b + (a + b) / c = 0) :
  (a + b + c) * (1 / a + 1 / b + 1 / c) = -3   :=  by sorry
