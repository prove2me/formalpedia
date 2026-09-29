-- Prove2me | Theorems.Thm_lean_workbook_plus_24199
-- name    : lean_workbook_plus_24199
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/877a5743-0e68-4ccd-b633-f0f957641ee7
-- statement:
--   Prove that $\sum_{i = 0}^{k}\binom{k}{i}p^{i}(1-p)^{k-i}= 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24199 (k : ℕ) (p : ℝ) : ∑ i in Finset.range (k+1), (Nat.choose k i : ℝ) * p ^ i * (1 - p) ^ (k - i) = 1   :=  by sorry
