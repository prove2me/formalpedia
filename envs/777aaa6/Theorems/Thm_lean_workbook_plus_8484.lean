-- Prove2me | Theorems.Thm_lean_workbook_plus_8484
-- name    : lean_workbook_plus_8484
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8e0670b5-e10a-44f5-a2ec-bbf74120fba0
-- statement:
--   Prove that there exists a constant $c$ such that $g(x+c)=g(x)$ for all real $x$ given $f(a,b)=f(a+b,b-a)$ and $g(x)=f(4^x,0)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8484 (f : ℝ × ℝ → ℝ) (a b : ℝ) (g : ℝ → ℝ) (h₁ : f (a, b) = f (a + b, b - a)) (h₂ : g x = f (4^x, 0)) : ∃ c, ∀ x, g (x + c) = g x   :=  by sorry
