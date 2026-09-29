-- Prove2me | Theorems.Thm_lean_workbook_plus_54702
-- name    : lean_workbook_plus_54702
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f0002d88-5e39-4c2d-8dfc-2efce79a82da
-- statement:
--   g(x)=\frac{f(x)-c}{\cos x}$ where $c=f(0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54702 (f : ℝ → ℝ) (c : ℝ) (g : ℝ → ℝ) (h₁ : ∀ x, g x = (f x - c) / Real.cos x) (h₂ : c = f 0) : ∀ x, g x = (f x - f 0) / Real.cos x   :=  by sorry
