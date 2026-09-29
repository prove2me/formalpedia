-- Prove2me | Theorems.Thm_lean_workbook_plus_32171
-- name    : lean_workbook_plus_32171
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b80dfb9f-d147-43d7-8d32-a8654ce03a36
-- statement:
--   Prove the identity: $\binom{n+m-1}{n}=\sum_{i=1}^{m}\binom{m}{i}\binom{n-1}{i-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32171 : ∀ n m : ℕ, n ≥ 1 ∧ m ≥ 1 → (n + m - 1).choose n = ∑ i in Finset.range m, (m).choose i * (n - 1).choose (i - 1)   :=  by sorry
