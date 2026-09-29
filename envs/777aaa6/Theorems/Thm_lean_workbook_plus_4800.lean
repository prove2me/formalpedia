-- Prove2me | Theorems.Thm_lean_workbook_plus_4800
-- name    : lean_workbook_plus_4800
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/04487958-502e-48a7-840f-7c80e8fcb1b4
-- statement:
--   Prove that $\binom{n}{n}+\binom{n}{n-1}+\binom{n}{n-2}+\cdots+\binom{n}{1} = 2^n - 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4800 (n : ℕ) : ∑ k in Finset.range n, choose n k = 2^n - 1   :=  by sorry
