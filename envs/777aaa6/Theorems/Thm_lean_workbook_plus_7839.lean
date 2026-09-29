-- Prove2me | Theorems.Thm_lean_workbook_plus_7839
-- name    : lean_workbook_plus_7839
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d17e1de1-9c3b-4359-8a67-3c2dda0f07f9
-- statement:
--   For two functions $f(x)=ax^2+bx+c$ and $g(x)=a^{'}x^2+b^{'}x+c^{'}$ , $f(x)=g(x)$ holds for all $x \in R$ if and only if $a=a^{'}$ , $b=b^{'}$ and $c=c^{'}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7839  (a b c a' b' c' : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c)
  (h₁ : ∀ x, g x = a' * x ^ 2 + b' * x + c')
  (h₂ : ∀ x, f x = g x) :
  a = a' ∧ b = b' ∧ c = c'   :=  by sorry
