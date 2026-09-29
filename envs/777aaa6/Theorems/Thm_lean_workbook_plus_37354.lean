-- Prove2me | Theorems.Thm_lean_workbook_plus_37354
-- name    : lean_workbook_plus_37354
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/87875972-a476-4244-8964-70b50e7be259
-- statement:
--   Prove $\forall \alpha \in \mathbb R^+ , \forall x\in (\alpha,+\infty), 4g(x)\le (g(x-\alpha)+g(\alpha))^2, g(x)=e^{f(x)}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37354 (f : ℝ → ℝ) (g : ℝ → ℝ) (h₁ : ∀ x, g x = Real.exp (f x)) (h₂ : ∀ α : ℝ, 0 < α → ∀ x : ℝ, x > α → 4 * g x ≤ (g (x - α) + g α) ^ 2) : ∀ α : ℝ, 0 < α → ∀ x : ℝ, x > α → 4 * Real.exp (f x) ≤ (Real.exp (f (x - α)) + Real.exp (f α)) ^ 2   :=  by sorry
