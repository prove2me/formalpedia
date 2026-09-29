-- Prove2me | Theorems.Thm_lean_workbook_plus_51131
-- name    : lean_workbook_plus_51131
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6bfe76a3-2a9b-415b-8dec-f03c9f851235
-- statement:
--   Show that $ \binom{n}{1}+\binom{n}{2}+\binom{n}{3}+...+\binom{n}{n}= 2^{n}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51131 (n : ℕ) : ∑ k in Finset.Icc 1 n, choose n k = 2^n - 1   :=  by sorry
