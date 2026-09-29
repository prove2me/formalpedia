-- Prove2me | Theorems.Thm_lean_workbook_plus_63323
-- name    : lean_workbook_plus_63323
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0e864601-6219-4483-b888-1972d760390c
-- statement:
--   We have $ 1+3+\cdots + \left(2n-1\right)=100.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63323 : ∑ k in Finset.range 50, (2 * k - 1) = 100   :=  by sorry
