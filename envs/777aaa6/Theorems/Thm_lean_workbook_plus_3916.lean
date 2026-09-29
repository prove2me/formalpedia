-- Prove2me | Theorems.Thm_lean_workbook_plus_3916
-- name    : lean_workbook_plus_3916
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/93980d0c-fb23-4f65-a757-f63fcee76c9e
-- statement:
--   Prove that $\sum_{k = 0}^{n} \binom{n}{k} = 2^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3916 (n : ℕ) : ∑ k in Finset.range (n + 1), (n.choose k) = 2 ^ n   :=  by sorry
