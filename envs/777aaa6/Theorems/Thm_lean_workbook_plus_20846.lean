-- Prove2me | Theorems.Thm_lean_workbook_plus_20846
-- name    : lean_workbook_plus_20846
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/fcabab36-d31c-4d8e-81a0-58a6645b5afc
-- statement:
--   Example 2 : $f(x)=x(1+\frac 12\sin(x))$ $\forall x\in(0,c)$ $f(x)=x+c$ $\forall x\ge c$ $g(x)=f(x)+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20846  (c : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : 0 < c)
  (h₁ : ∀ x ∈ Set.Ioo 0 c, f x = x * (1 + Real.sin x / 2))
  (h₂ : ∀ x ≥ c, f x = x + c)
  (h₃ : ∀ x, g x = f x + c) :
  ∃ x, x > c ∧ g x < g c   :=  by sorry
