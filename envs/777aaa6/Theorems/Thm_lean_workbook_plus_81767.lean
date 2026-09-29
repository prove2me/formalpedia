-- Prove2me | Theorems.Thm_lean_workbook_plus_81767
-- name    : lean_workbook_plus_81767
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/771d98f2-d174-49ce-94b5-803e6192bb72
-- statement:
--   Calculate the sum: $g(50) = f(1) + f(2) + ... + f(50)$ where $f(x) = \frac{1}{(x+1)(x+2)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81767 (f : ℕ → ℝ) (g : ℕ → ℝ) (h₁ : ∀ x, f x = 1/((x+1)*(x+2))) (h₂ : g 50 = ∑ k in Finset.range 50, f k) : g 50 = 25/52   :=  by sorry
