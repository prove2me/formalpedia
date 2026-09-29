-- Prove2me | Theorems.Thm_lean_workbook_plus_11133
-- name    : lean_workbook_plus_11133
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e26ed41b-d943-490f-8d24-971bff4b5ac8
-- statement:
--   Evaluate $2^2+4^2+6^2+8^2+\cdots+50^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11133 (n : ℕ) : ∑ i in Finset.range 25, (2 * i + 2)^2 = 24600   :=  by sorry
