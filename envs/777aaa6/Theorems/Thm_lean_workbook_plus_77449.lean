-- Prove2me | Theorems.Thm_lean_workbook_plus_77449
-- name    : lean_workbook_plus_77449
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/505724b5-dcc0-4a14-a9f2-f84526a21fa5
-- statement:
--   Prove that $f(x)=\frac{1}{3}+a \times (\frac{1}{2x+1}-\frac{1}{3}) = a\times \frac{1}{2x+1} + (1-a) \frac{1}{3}$ for some constant $a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77449 (f : ℝ → ℝ) (a : ℝ) (h₁ : ∀ x, f x = 1/3 + a * (1/(2*x + 1) - 1/3)) : ∀ x, f x = a * 1/(2*x + 1) + (1 - a) * 1/3   :=  by sorry
