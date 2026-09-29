-- Prove2me | Theorems.Thm_lean_workbook_plus_73446
-- name    : lean_workbook_plus_73446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d9834aa8-3de8-4284-94a0-fd3dbc1ec37c
-- statement:
--   For real numbers a,b,c,d, the polynomial p(x) has the form of: $p(x)=x^4+ax^3+bx^2+cx+d$ That satisfies: $p(1)=827$ $p(2)=1654$ $p(3)=2481$ Find the value of $\frac{p(9)+p(-5)}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73446 (a b c d : ℝ) (p : ℝ → ℝ) (hp : p = fun x : ℝ => x^4 + a*x^3 + b*x^2 + c*x + d) : p 1 = 827 ∧ p 2 = 1654 ∧ p 3 = 2481 → (p 9 + p (-5)) / 4 = 2003   :=  by sorry
