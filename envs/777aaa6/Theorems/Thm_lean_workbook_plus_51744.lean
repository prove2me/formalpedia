-- Prove2me | Theorems.Thm_lean_workbook_plus_51744
-- name    : lean_workbook_plus_51744
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/aa74c5b8-6c45-4b25-9dcc-cc751d3edd28
-- statement:
--   To determine values of $f(x)$ for non-integers $x$ that are rational, assume $f\\left(\\frac{a}{b} \\right)=c \neq \pm 1$ with $\gcd(a,b)=1$ and $b \neq \pm 1$ . $P\\left(x, \frac{a}{b} \\right) \implies f(x+c)=cf(x)$ . Using induction, we can show that $f(nc)=c^n$ for integers $n$ , so $f\\left(b\\left(\\frac{a}{b} \\right) \\right)=f(a)=c^b$ . Since $a$ is an integer, we have $f(a)=1$ , which contradicts $c \neq \pm 1$ . Therefore, $f(x)= 1$ or $-1$ for each non-integer $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51744  (f : ℝ → ℝ)
  (h₀ : ∀ x, (¬ ∃ a : ℤ, x = a) → (f x = 1 ∨ f x = -1)) :
  ∀ x, (¬ ∃ a : ℤ, x = a) → f x = 1 ∨ f x = -1   :=  by sorry
