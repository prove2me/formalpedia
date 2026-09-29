-- Prove2me | Theorems.Thm_lean_workbook_plus_26187
-- name    : lean_workbook_plus_26187
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2be5075f-c8ca-4d4f-9bbb-97ed94b774a8
-- statement:
--   Calculate the sum of the series $\sum_{x=1}^{12} x(25-x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26187 (f : ℕ → ℕ) : ∑ x in Finset.Icc 1 12, x * (25 - x) = 150   :=  by sorry
