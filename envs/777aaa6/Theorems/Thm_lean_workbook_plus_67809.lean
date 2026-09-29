-- Prove2me | Theorems.Thm_lean_workbook_plus_67809
-- name    : lean_workbook_plus_67809
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ede51057-48fc-4e90-995a-8cc37eda7a47
-- statement:
--   The sum of this from \(k+1=4\) to \(k+1=52\) is equal to 1 since \(k+1\) must occur in one of those positions. So \(\binom{53}{5}=\sum_{k=3}^{51}\binom{k}{3}\cdot \binom{52-k}{1}\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67809 (n : ℕ) : ∑ k in Finset.Icc 3 51, (Nat.choose k 3 * Nat.choose (52 - k) 1) = Nat.choose 53 5   :=  by sorry
