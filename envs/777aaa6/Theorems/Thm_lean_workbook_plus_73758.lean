-- Prove2me | Theorems.Thm_lean_workbook_plus_73758
-- name    : lean_workbook_plus_73758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/130e552d-06f8-4f57-aeeb-f9dfa5560c51
-- statement:
--   Regard this as a linear system with the solution $(1,2,3)$ : \n \n \begin{eqnarray}1+{2\over b}-{3\over c} &=& a\\-{1\over a}+2+{3\over c} &=& b\\{1\over a}-{2\over b}+3 &=& c\end{eqnarray} \n Adding up all the equations we get $a+b+c=6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73758  (a b c : ℝ)
  (h₀ : 1 + 2 / b - 3 / c = a)
  (h₁ : -1 / a + 2 + 3 / c = b)
  (h₂ : 1 / a - 2 / b + 3 = c) :
  a + b + c = 6   :=  by sorry
