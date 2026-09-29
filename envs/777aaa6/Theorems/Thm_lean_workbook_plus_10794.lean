-- Prove2me | Theorems.Thm_lean_workbook_plus_10794
-- name    : lean_workbook_plus_10794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2b77a418-fcd9-4c3f-8be0-9a3e9ede02f2
-- statement:
--   Case 2: Do you mean, find $\frac{1}{2a} +\frac{1}{2b}$ \nIf yes then, \n $\frac{1}{2a} +\frac{1}{2b} =\frac{1}{2} (\frac{1}{a} +\frac{1}{b}) => \frac{1}{2} (\frac{a+b}{ab})$ \nnow, $ab=\frac{7}{2}$ and $a+b=4$ \n $\frac{1}{2} (\frac{a+b}{ab}) =\boxed{\frac{4}{7}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10794  (a b : ℝ)
  (h₀ : a + b = 4)
  (h₁ : a * b = 7 / 2) :
  1 / (2 * a) + 1 / (2 * b) = 4 / 7   :=  by sorry
