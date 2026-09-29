-- Prove2me | Theorems.Thm_lean_workbook_plus_72787
-- name    : lean_workbook_plus_72787
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b0b713e8-014d-4fc9-8b9e-c8ad65154853
-- statement:
--   We can solve these problems using the formula for harmonic mean, $\frac{2}{\frac{1}{a}+\frac{1}{b}} = 30$ . Let $x$ be the number of minutes that Bertha uses. We already have one rate, so we solve for the second. \n\n $\frac{2}{\frac{1}{40}+\frac{1}{b}} = 30$ \n\n $\frac{80b}{b+40} = 30$ \n\n $80b = 30b+1200$ \n\n $50b = 1200$ \n\n $b = 24$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72787  (b : ℝ)
  (h₀ : 0 < b)
  (h₁ : 2 / (1 / 40 + 1 / b) = 30) :
  b = 24   :=  by sorry
