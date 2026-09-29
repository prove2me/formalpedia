-- Prove2me | Theorems.Thm_lean_workbook_plus_6475
-- name    : lean_workbook_plus_6475
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/1a4fb28f-a41b-4fe8-a50a-4448f25742f2
-- statement:
--   Calculate the summation: $\sum_{i = 5}^{78} i^2 - i + 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6475 (f : ℕ → ℕ) : ∑ i in Finset.Icc 5 78, (i^2 - i + 3) = 158360   :=  by sorry
