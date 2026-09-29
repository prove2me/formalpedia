-- Prove2me | Theorems.Thm_lean_workbook_plus_73289
-- name    : lean_workbook_plus_73289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/90cd713e-85cf-4add-bf05-d60cababe7c4
-- statement:
--   For $f(1) = 1$ , $f(x^2) = [f(x)]^2$ . This implies that $f(x)$ is nonnegative whenever $x$ is nonnegative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73289  (f : ℝ → ℝ)
  (h₀ : f 1 = 1)
  (h₁ : ∀ x, f (x^2) = (f x)^2) :
  ∀ x ≥ 0, 0 ≤ f x   :=  by sorry
