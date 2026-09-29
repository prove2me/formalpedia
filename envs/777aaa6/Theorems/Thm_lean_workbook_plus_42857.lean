-- Prove2me | Theorems.Thm_lean_workbook_plus_42857
-- name    : lean_workbook_plus_42857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b07a0ef1-6827-4999-97d5-d3f6fcd3b8ae
-- statement:
--   ObservationYou could use the observation that: \n\nFor any $x \in \mathbb{R^+}$ : \n\n $x^5 - x^2 + 3 \geq x^3 + 2 \Rightarrow$ $\frac{1}{x^5 - x^2 + 3} \leq \frac{1}{x^3 + 2}$ \n\n<https://artofproblemsolving.com/community/c6h5383p17397>
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42857  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^5 - x^2 + 3 ≥ x^3 + 2) :
  1 / (x^5 - x^2 + 3) ≤ 1 / (x^3 + 2)   :=  by sorry
