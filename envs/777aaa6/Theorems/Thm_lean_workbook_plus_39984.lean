-- Prove2me | Theorems.Thm_lean_workbook_plus_39984
-- name    : lean_workbook_plus_39984
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0cbe4b4d-1b47-40e0-9153-223779896ca5
-- statement:
--   How to get $f(x)=3x+a$ and $g(x)=\frac x3+b$ with $a+3b=12$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39984 (f g : ℝ → ℝ) (hf : ∀ x, f x = 3 * x + a) (hg : ∀ x, g x = x / 3 + b) (h : a + 3 * b = 12) : ∃ a b : ℝ, a + 3 * b = 12 ∧ ∀ x, f x = 3 * x + a ∧ g x = x / 3 + b   :=  by sorry
