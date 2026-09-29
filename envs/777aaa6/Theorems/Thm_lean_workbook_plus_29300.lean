-- Prove2me | Theorems.Thm_lean_workbook_plus_29300
-- name    : lean_workbook_plus_29300
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/07b2d230-0f66-4e2a-bb8c-efbe376b82a2
-- statement:
--   Find the value of $10^2+11^2+12^2+...+94^2+95^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29300 (n : ℕ) : ∑ i in Finset.Icc 10 95, (i ^ 2) = 290035   :=  by sorry
