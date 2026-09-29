-- Prove2me | Theorems.Thm_lean_workbook_plus_75457
-- name    : lean_workbook_plus_75457
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/155f527f-b1bd-431f-8a06-ad75f6c63a79
-- statement:
--   Let $f(x) = p(x) - q(x)$; then we have that $f(1) = 0, f(2) = 1$ and $f(3) = 4$. Let $f(4) = y$. The first finite differences are $f(2) - f(1) = 1$, $f(3) - f(2) = 3$ and $f(4) - f(3) = y-4$. The second finite differences are $3-1 = 2$ and $(y-4)-3=y-7$. Since $f(x)$ is a polynomial of power $2$, it must have a constant 2nd finite difference, i.e. $y-7 = 2$. Thus, we get that $y = f(4) = p(4)-q(4) = \boxed{9}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75457  (p q : ℝ → ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = p x - q x)
  (h₁ : f 1 = 0)
  (h₂ : f 2 = 1)
  (h₃ : f 3 = 4)
  (h₄ : f 4 = y)
  (h₅ : y - 4 - 3 = 2) :
  y = 9   :=  by sorry
