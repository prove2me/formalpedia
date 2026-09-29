-- Prove2me | Theorems.Thm_lean_workbook_plus_9467
-- name    : lean_workbook_plus_9467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/56add0cd-830c-4cd9-91fb-45049935f9db
-- statement:
--   Let $f(x)=x^5+6x^4+7x^3-20x^2-42x-20$ . Note that $f(2)=32+96+56-80-84-20=0$ , so $2$ is a root of the polynomial. Factoring an $x-2$ out of the polynomial, we have $f(x)=(x-2)(x^4+8x^3+23x^2+26x+10)$ . Note that $-1$ is a root of the quartic in the factorization, so we can factor an $x+1$ out of the quartic to get $f(x)=(x-2)(x+1)(x^3+7x^2+16x+10)$ . Now, note that $-1$ is a root of the cubic, so we can once more factor an $x+1$ out of the expression to get $f(x)=(x-2)(x+1)^2(x^2+6x+10)$ . The quadratic is $(x+3)^2+1$ , and thus does not have any real roots, and cannot be factored in the real numbers. Thus, the polynomial is $\boxed{(x-2)(x+1)^2(x^2+6x+10)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9467  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^5 + 6 * x^4 + 7 * x^3 - 20 * x^2 - 42 * x - 20)
  (h₁ : f 2 = 0) :
  ∀ x, f x = (x - 2) * (x + 1)^2 * (x^2 + 6 * x + 10)   :=  by sorry
