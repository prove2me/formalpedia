-- Prove2me | Theorems.Thm_lean_workbook_plus_20139
-- name    : lean_workbook_plus_20139
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bd9117b0-cfcf-47e4-8899-59eeae1c9a32
-- statement:
--   Prove that $\ln(x)+\ln(y)=\ln(xy)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20139 : ∀ x y : ℝ, x > 0 ∧ y > 0 → Real.log x + Real.log y = Real.log (x*y)   :=  by sorry
