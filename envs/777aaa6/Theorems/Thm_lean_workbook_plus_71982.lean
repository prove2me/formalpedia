-- Prove2me | Theorems.Thm_lean_workbook_plus_71982
-- name    : lean_workbook_plus_71982
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f085705c-463e-423c-a82f-ecb79bd7e46f
-- statement:
--   Prove that $ \sum_{k=0}^{n}{\binom{n}k}\times{2^k} = 3^n $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71982 (n : ℕ) : ∑ k in Finset.range (n+1), (Nat.choose n k) * 2^k = 3^n   :=  by sorry
