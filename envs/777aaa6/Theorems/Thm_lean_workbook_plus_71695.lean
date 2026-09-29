-- Prove2me | Theorems.Thm_lean_workbook_plus_71695
-- name    : lean_workbook_plus_71695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d1ec227e-63bc-401c-852e-a6a9e9ca4070
-- statement:
--   And solutions $\boxed{x\in\left\{-\frac 32,-\frac 12\right\}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71695  (x : ℝ)
  (h₀ : x^2 + 2 * x + 3 / 4 = 0) :
  x = -3 / 2 ∨ x = -1 / 2   :=  by sorry
