-- Prove2me | Theorems.Thm_lean_workbook_plus_22341
-- name    : lean_workbook_plus_22341
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7386a754-47f7-47f9-b5ab-414c7ae958a7
-- statement:
--   Being a function linear we have that $$ \frac{f(n)}{n} = k $$ , with k constant, on the other hand the expression is equivalent to $$ \frac{f(x ^ 2-y ^ 2)}{x ^ 2-y ^ 2} = \frac {f(x)}{x}. \frac{f(2y)}{2y}$$ , then $ k = k ^ 2 $ , then k∈ {0, 1}, if k = 0, then $ f (n) = 0 $ , If k = 1 then, $ f (n) = n $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22341  (f : ℤ → ℤ)
  (h₀ : ∃ k, ∀ n, f n = k * n)
  (h₁ : ∀ x y, f (x^2 - y^2) = f x * f (2 * y)) :
  ∀ n, f n = 0 ∨ ∀ n, f n = n   :=  by sorry
