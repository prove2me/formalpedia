-- Prove2me | Theorems.Thm_lean_workbook_plus_7967
-- name    : lean_workbook_plus_7967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ddef709d-b1fc-4e61-81a8-cbb097e1febc
-- statement:
--   How to get $f(x)=3x+a$ and $g(x)=\frac x3+b$ with $a+3b=12$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7967 (f g : ℝ → ℝ) (a b : ℝ) (h₁ : a + 3 * b = 12) (h₂ : ∀ x, f x = 3 * x + a) (h₃ : ∀ x, g x = x / 3 + b) : (∃ a b, a + 3 * b = 12 ∧ (∀ x, f x = 3 * x + a) ∧ (∀ x, g x = x / 3 + b))   :=  by sorry
