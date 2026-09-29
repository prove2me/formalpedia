-- Prove2me | Theorems.Thm_lean_workbook_plus_28079
-- name    : lean_workbook_plus_28079
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6847e351-198a-4120-9266-1fcc87927aee
-- statement:
--   Prove that $2^n \binom{n+1}{n}-2^{n-1}\binom{n+1}{n-1}\ldots (-1)^n 2^0\binom{n+1}{0} = 2^{n+1}-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28079 : ∀ n : ℕ, (∑ i in Finset.range (n+1), (-1 : ℤ)^i * 2^(n-i) * (n + 1).choose i) = 2^(n+1) - 1   :=  by sorry
