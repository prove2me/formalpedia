-- Prove2me | Theorems.Thm_lean_workbook_plus_64903
-- name    : lean_workbook_plus_64903
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/999d9f59-d276-4574-b647-bf9738694958
-- statement:
--   Prove the identity $\cos(2y) = 2\cos^{2}(y) - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64903 (y : ℝ) : Real.cos (2 * y) = 2 * (Real.cos y)^2 - 1   :=  by sorry
