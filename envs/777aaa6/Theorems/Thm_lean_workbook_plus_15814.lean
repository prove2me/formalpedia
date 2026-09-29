-- Prove2me | Theorems.Thm_lean_workbook_plus_15814
-- name    : lean_workbook_plus_15814
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/feec0803-581b-4ea4-b797-7b122aae9bff
-- statement:
--   And when $f(x)=-x^3+ax^2+bx+c=-(x-2)^3+\frac{3}{4}(x-2),$ where $a=6,b=-\frac{45}{4},c=\frac{13}{2},$ we have $M=\frac{1}{4}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15814  (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = -x^3 + a * x^2 + b * x + c)
  (h₁ : a = 6)
  (h₂ : b = -45 / 4)
  (h₃ : c = 13 / 2)
  (h₄ : ∀ x, f x = -(x - 2)^3 + (3 / 4) * (x - 2)) :
  ∃ x, (f x = 0 ∧ 0 < x ∧ x < 1)   :=  by sorry
