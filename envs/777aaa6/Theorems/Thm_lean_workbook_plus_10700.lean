-- Prove2me | Theorems.Thm_lean_workbook_plus_10700
-- name    : lean_workbook_plus_10700
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/7a6e374e-bd24-4d2b-b56c-68510c687b7c
-- statement:
--   Find all functions $f$ of two variables, whose arguments $x,y$ and values $f(x,y)$ are positive integers, satisfying the following conditions (for all positive integers $x$ and $y$ ): \n\n \begin{align*} f(x,x)& =x,\ f(x,y)& =f(y,x),\ (x+y)f(x,y)& =yf(x,x+y).\end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10700 (f : ℕ → ℕ → ℕ) (hf : ∀ x y : ℕ, f x y > 0 ∧ f x x = x ∧ f x y = f y x ∧ (x + y) * f x y = y * (f x (x + y))) : ∀ x y : ℕ, f x y = Nat.gcd x y   :=  by sorry
