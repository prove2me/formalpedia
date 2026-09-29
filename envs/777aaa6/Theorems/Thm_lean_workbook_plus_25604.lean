-- Prove2me | Theorems.Thm_lean_workbook_plus_25604
-- name    : lean_workbook_plus_25604
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6d502f5a-b00c-4b8e-b798-5f5cd4ca4b33
-- statement:
--   Determine all functions $ f$ defined in the set of rational numbers and taking their values in the same set such that the equation $ f(x + y) + f(x - y) = 2f(x) + 2f(y)$ holds for all rational numbers $x$ and $y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25604 (f : ℚ → ℚ) (hf: f (x + y) + f (x - y) = 2 * f x + 2 * f y) : ∃ a b :ℚ, f x = a * x + b   :=  by sorry
