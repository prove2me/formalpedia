-- Prove2me | Theorems.Thm_lean_workbook_plus_25471
-- name    : lean_workbook_plus_25471
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/29735b2d-9390-4b8a-8822-18d43c15505c
-- statement:
--   $\sqrt{\frac{2}{3}}-\frac{1}{6} \le (1-a)(1-b)+\frac{a}{1+2b}+\frac{b}{1+2a}\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25471 : ∀ a b : ℝ, Real.sqrt (2 / 3) - 1 / 6 ≤ (1 - a) * (1 - b) + a / (1 + 2 * b) + b / (1 + 2 * a) ∧ (1 - a) * (1 - b) + a / (1 + 2 * b) + b / (1 + 2 * a) ≤ 1   :=  by sorry
