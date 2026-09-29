-- Prove2me | Theorems.Thm_lean_workbook_plus_1844
-- name    : lean_workbook_plus_1844
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/98d30775-bfdc-4003-92c8-e9715246594a
-- statement:
--   The $256^\text{th}$ number is found by summing binomial coefficients: $\binom{9}{1}+...\binom{9}{9}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1844 (n : ℕ) (hn : n = 9) : ∑ k in Finset.range n, Nat.choose n k = 2^9   :=  by sorry
