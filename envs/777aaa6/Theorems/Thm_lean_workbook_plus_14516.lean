-- Prove2me | Theorems.Thm_lean_workbook_plus_14516
-- name    : lean_workbook_plus_14516
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8a7e1ad8-3d2f-4ff9-bafc-1c7e8e976ccd
-- statement:
--   Another solutionReplacing $y$ with $xy$ and a bit of manipulation, we get: \n\n $$ 2xy = f(x+y) - f(x) - \frac{f(xy)}{f(x)} \ldots(1)$$ \n\nIn particular, $f(x+y) > f(x)$ for all $x, y\in \mathbb{Q}^+$ , so $f$ is strictly increasing and thus injective. Intertwining between $x$ and $y$ gives us $f(x) + \frac{f(xy)}{f(x)} = f(y) + \frac{f(xy)}{f(y)}$ . Solving this gives us $f(xy) = f(x)f(y)$ whenever $x\neq y$ (as $f$ is injective). To generalize this result, notice that $f(1) f(2) = f(2)$ so $f(1) = 1$ , and for $x\neq 1$ ,: \n\n $$ f(x^3) f(x^2) = f(x^5) = f(x^4) f(x) = f(x^3) f(x)^2 $$ \n\nHence, $f(x^2) = f(x)^2$ , so indeed $f(xy) = f(x) f(y)$ for all $x, y\in \mathbb{Q}$ . Equation $(1)$ now becomes: \n\n $$ 2xy = f(x+y) - f(x) - f(y) $$ $$ (f(x+y) - (x+y)^2) - (f(x) - x^2) - (f(y) - y^2) = 0 $$ \n\nso the function $x\mapsto (f(x) - x^2)$ is additive. Since it's domain is $\mathbb{Q}^+$ , it must be linear; there exists a rational number $c$ such that $f(x) = x^2 + cx = x(x+c)$ for all $x\in \mathbb{Q}^+$ . Since we obtained $f(1) = 1$ , this means $c = 0$ , so $f(x) = x^2 \; \forall x\in \mathbb{Q}^+$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14516  (f : ℚ → ℝ)
  (h₀ : ∀ x > 0, f x > 0)
  (h₁ : ∀ x > 0, 2 * x = f (x + 1) - f x - f (x * 1))
  (h₂ : ∀ x > 0, ∀ y > 0, f (x * y) = f x * f y) :
  ∀ x > 0, f x = x^2   :=  by sorry
