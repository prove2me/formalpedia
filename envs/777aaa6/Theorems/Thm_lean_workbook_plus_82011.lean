-- Prove2me | Theorems.Thm_lean_workbook_plus_82011
-- name    : lean_workbook_plus_82011
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2bbb4dc0-fe15-4e58-a5e7-b6dee220574c
-- statement:
--   Look at the fixed point of function , $x^2 -2 =x$ ... Fixed point is the point at which $f(x)=x$ . If we solve the equation $f(x)=x$ , with $f(x)=x^2-2$ . We get $x=-1$ or $x=2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82011  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 2)
  (h₁ : f x = x) :
  x = -1 ∨ x = 2   :=  by sorry
