-- Prove2me | Theorems.Thm_lean_workbook_plus_51689
-- name    : lean_workbook_plus_51689
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/cadb65de-00dc-47a4-88ff-aec2c984e4f9
-- statement:
--   Find the sum of the series $n^2 + 3n + 2$ for $n = 1, 2, 3, ..., 10$, where $n$ is a positive integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51689 (n : ℕ) : ∑ i in Finset.Icc 1 10, (i^2 + 3*i + 2) = 570   :=  by sorry
