-- Prove2me | Theorems.Thm_lean_workbook_plus_69392
-- name    : lean_workbook_plus_69392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6459ddb0-5aab-443c-875f-fe39618aabf0
-- statement:
--   we have: $ \frac{1}{\frac{1}{a^2}}+\frac{1}{\frac{1}{b^2}}+\frac{1}{\frac{1}{c^2}} \geq \frac{9}{\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}}$ \nhence, $ \frac{1}{9} \left(a^2+b^2+c^2 \right) \geq \frac{1}{\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69392  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  1 / 9 * (a^2 + b^2 + c^2) ≥ 1 / (1 / a^2 + 1 / b^2 + 1 / c^2)   :=  by sorry
