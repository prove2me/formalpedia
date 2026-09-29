-- Prove2me | Theorems.Thm_lean_workbook_plus_39800
-- name    : lean_workbook_plus_39800
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7ab3c928-93b8-451a-8ba6-0813a0f311af
-- statement:
--   Take $ f(x)=0$ and $ g(x)=2x+100$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39800  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 0)
  (h₁ : ∀ x, g x = 2 * x + 100)
  (h₂ : 0 ≤ x) :
  f x < g x   :=  by sorry
