-- Prove2me | Theorems.Thm_lean_workbook_plus_38482
-- name    : lean_workbook_plus_38482
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/023acf06-b854-4689-a1c3-d57055b0ef1b
-- statement:
--   Find the interval where the function $f(x)=e^{|x^2-4x+3|}$ increases and decreases.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38482 (f : ℝ → ℝ) (hf: f x = e^(|x^2 - 4*x + 3|)) : ∀ x y: ℝ, x < y → f x ≤ f y ∨ f x ≥ f y   :=  by sorry
