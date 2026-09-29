-- Prove2me | Theorems.Thm_lean_workbook_plus_16182
-- name    : lean_workbook_plus_16182
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e9291864-a899-4b5f-b2e1-ab170281cb1b
-- statement:
--   $\binom{n}{0} + \binom{n}{1} + \binom{n}{2} + ... +\binom{n}{n} = (1+1)^{n} = 2^{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16182 (n : ℕ) : ∑ k in Finset.range (n+1), (Nat.choose n k) = 2^n   :=  by sorry
