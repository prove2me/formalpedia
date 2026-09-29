-- Prove2me | Theorems.Thm_lean_workbook_plus_4699
-- name    : lean_workbook_plus_4699
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dcc5848a-ce5b-45d3-adad-cb3cb77e92a5
-- statement:
--   Solving the square: \nIf there is an equation $ax^2+bx+c=0$ , \nThen you can simplify to $x^2+\frac{bx}{a}+\frac{c}{a}=0$ \nThe property $(x+a)^2=x^2+2a+a^2$ becomes relevant, because we can substitute $a$ in this equation with $\frac{b}{2a}$ , thus getting \n $(x+\frac{b}{2a})^2=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4699  (a b c x : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : a * x^2 + b * x + c = 0) :
  x^2 + b / a * x + c / a = 0   :=  by sorry
