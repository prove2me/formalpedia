-- Prove2me | Theorems.Thm_lean_workbook_plus_23895
-- name    : lean_workbook_plus_23895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a1bc4dd2-64c8-495b-8acf-2f708da40da0
-- statement:
--   Rearranging yields $y=\frac{x^{2}+4}{12} = \frac{1}{12}x^{2}+\frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23895 (x y : ℝ) (h₁ : y = (x^2 + 4)/12) : y = 1/12 * x^2 + 1/3   :=  by sorry
