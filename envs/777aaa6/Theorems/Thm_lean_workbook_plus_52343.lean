-- Prove2me | Theorems.Thm_lean_workbook_plus_52343
-- name    : lean_workbook_plus_52343
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5947c8af-fe7b-446a-8d75-a63be1ce0b7d
-- statement:
--   Take logarithms: $\ln\left(1+\frac1n\right)^{n}=n\ln\left(1+\frac1n\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52343 : ∀ n : ℕ, Real.log (1 + 1 / n)^n = n * Real.log (1 + 1 / n)   :=  by sorry
