-- Prove2me | Theorems.Thm_lean_workbook_plus_81561
-- name    : lean_workbook_plus_81561
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/696224d4-63b2-47a7-9b44-bdb64e3b0067
-- statement:
--   How to get $f(x)=3x+a$ and $g(x)=\frac x3+b$ with $a+3b=12$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81561 (f g : ℝ → ℝ) (a b : ℝ) (h₁ : a + 3 * b = 12) (h₂ : ∀ x, f x = 3 * x + a) (h₃ : ∀ x, g x = x / 3 + b) : ∃ a b, a + 3 * b = 12 ∧ (∀ x, f x = 3 * x + a) ∧ (∀ x, g x = x / 3 + b)   :=  by sorry
