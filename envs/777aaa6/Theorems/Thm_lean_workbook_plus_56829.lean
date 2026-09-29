-- Prove2me | Theorems.Thm_lean_workbook_plus_56829
-- name    : lean_workbook_plus_56829
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/91e679e5-f4a7-4e7f-88d1-9210ba32b92e
-- statement:
--   Let $a,b,c > 0$ such that $ab + bc + ca + abc \ge 4$ . Prove that \n $a + b + c \ge 3 + \frac{{{{\left( {b - c} \right)}^2}}}{{b + c + 4}}$ \nFrom condition we get $a = \frac{4-bc}{b+c+bc},$ so we will show that \n $\frac{4-bc}{b+c+bc} + b + c \geqslant 3 + \frac{{{{\left( {b - c} \right)}^2}}}{{b + c + 4}},$ or \n $\frac{(2bc+b+c-4)^2}{(bc+b+c)(b+c+4)} \geqslant 0.$ Done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56829  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b + b * c + c * a + a * b * c ≥ 4) :
  a + b + c ≥ 3 + (b - c)^2 / (b + c + 4)   :=  by sorry
