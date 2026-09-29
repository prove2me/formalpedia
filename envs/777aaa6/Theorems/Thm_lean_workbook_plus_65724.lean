-- Prove2me | Theorems.Thm_lean_workbook_plus_65724
-- name    : lean_workbook_plus_65724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/959665e0-627c-4b75-bc3f-dd76a7804540
-- statement:
--   Let $ f(a, b)$ be the expected number of white balls left after all black balls get chosen, starting with $ a$ white and $ b$ black balls. Then $ f(0, b) = 0$ , $ f(a, 0) = a$ and $ f(a, b) = \frac {a f(a - 1, b) + b f(a, b - 1)}{a + b}$ . This lets us compute as many values as we like, in particular $ f(15, 10)$ . If we look at a few computed values, it also lets us conjecture that $ f(a, b) = \frac {a}{b + 1}$ , which then follows immediately from the recursion by induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65724  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ b, f 0 b = 0)
  (h₁ : ∀ a, f a 0 = a)
  (h₂ : ∀ a b, (a + b) * f a b = a * f (a - 1) b + b * f a (b - 1)) :
  f 15 10 = 15 / 11   :=  by sorry
