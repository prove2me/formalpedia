-- Prove2me | Theorems.Thm_lean_workbook_plus_72207
-- name    : lean_workbook_plus_72207
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e0bb838b-f7e6-4cfe-90a9-a5ad1fa8fa94
-- statement:
--   Find the sum of the arithmetic sequence $2+\cdots +7$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72207 : ∑ k in Finset.Icc 2 7, k = 27   :=  by sorry
