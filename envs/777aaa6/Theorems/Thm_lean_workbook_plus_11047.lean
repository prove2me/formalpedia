-- Prove2me | Theorems.Thm_lean_workbook_plus_11047
-- name    : lean_workbook_plus_11047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/aa110f7f-8279-49dc-b39e-b90c85e684cd
-- statement:
--   For $a+b+c>=\frac{1}{a}+\frac{1}{b}+\frac{1}{c})$ , we have\n\n $(a+b+c)^2 >= (a+b+c)(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}) >= 9$ .\n\nAnd with the Power--Mean Inequality, we get\n\n $(\frac{a^3+b^3+c^3}{3})^{\frac{1}{3}}>=\frac{a+b+c}{3}$ ,\n\nThe above inequality is equivalent to\n\n $a^3+b^3+c^3>=\frac{(a+b+c)^3}{9}$ .\n\nIn order to prove the origin inequality, we only need prove the inequality as follows.\n\n $\frac{(a+b+c)^3}{9}>=a+b+c $ \n\nThe inequality is exactly the inequality\n\n $(a+b+c)^2 >= 9$ .\n\nThus, the proof of the origin inequality is completed.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11047  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c ≥ 1 / a + 1 / b + 1 / c) :
  a^3 + b^3 + c^3 ≥ (a + b + c)^3 / 9   :=  by sorry
