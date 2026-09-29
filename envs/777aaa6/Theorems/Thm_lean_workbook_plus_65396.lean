-- Prove2me | Theorems.Thm_lean_workbook_plus_65396
-- name    : lean_workbook_plus_65396
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4cb8bd24-8031-4334-9210-30529a338f96
-- statement:
--   Prove the following: $1+2+4+8...+2^n=2^{n+1}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65396 : ∀ n, ∑ i in Finset.range n, 2 ^ i = 2 ^ (n + 1) - 1   :=  by sorry
