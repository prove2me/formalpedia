-- Prove2me | Theorems.Thm_lean_workbook_plus_14542
-- name    : lean_workbook_plus_14542
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a4da4ed9-74ba-4f0b-9a2e-fddba67cec37
-- statement:
--   $ab+c(a+b)=9$ we see that $a,b$ satisfy $a+b=6-c$ and $ab=(c-3)^2$ so $a$ and $b$ are the roots of $f(x)=x^2+(c-6)x+(c-3)^2=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14542  (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 + (c - 6) * x + (c - 3)^2)
  (h₁ : f a = 0)
  (h₂ : f b = 0)
  (h₃ : a + b = 6 - c)
  (h₄ : a * b = (c - 3)^2) :
  9 = a * b + c * (a + b)   :=  by sorry
