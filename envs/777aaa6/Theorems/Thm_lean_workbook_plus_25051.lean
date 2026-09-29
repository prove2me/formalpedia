-- Prove2me | Theorems.Thm_lean_workbook_plus_25051
-- name    : lean_workbook_plus_25051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d4af64a8-5762-4019-84ab-f13218cd96b9
-- statement:
--   Find the value of $\frac{f(12)+f(-8)}{10}$ given $f(x)= x^4+ax^3+bx^2+cx+d$ such that $f(1)=10, f(2)=20, f(3)=30$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25051 (a b c d : ℝ) (f : ℝ → ℝ) (hf: f = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : f 1 = 10 ∧ f 2 = 20 ∧ f 3 = 30 → (f 12 + f (-8)) / 10 = 1984   :=  by sorry
