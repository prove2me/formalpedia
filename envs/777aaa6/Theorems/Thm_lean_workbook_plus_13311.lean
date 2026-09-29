-- Prove2me | Theorems.Thm_lean_workbook_plus_13311
-- name    : lean_workbook_plus_13311
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0cc382b2-5442-4618-94f0-4a0b8398c599
-- statement:
--   Apply Gauss' Formula to find the sum $1+2+3+...+12$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13311 : ∑ i in Finset.range 13, i = 78   :=  by sorry
