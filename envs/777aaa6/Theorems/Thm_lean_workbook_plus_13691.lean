-- Prove2me | Theorems.Thm_lean_workbook_plus_13691
-- name    : lean_workbook_plus_13691
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/e433bf2e-f0a6-4911-9a23-7c7c8c33715f
-- statement:
--   We proceed by showing that the LHS=RHS. $\sum_{k=0}^{n} \binom{n}{k}^2$ $=\sum_{k=0}^{n} \binom{n}{k}\binom{n}{k}$ We use the identity $\binom{n}{k}=\binom{n}{n-k}$ $=\sum_{k=0}^{n} \binom{n}{k}\binom{n}{n-k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13691 (n : ℕ) : ∑ k in Finset.range (n+1), (Nat.choose n k)^2 = ∑ k in Finset.range (n+1), Nat.choose n k * Nat.choose n (n - k)   :=  by sorry
