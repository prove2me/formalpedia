-- Prove2me | Theorems.Thm_lean_workbook_plus_66834
-- name    : lean_workbook_plus_66834
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/24c38610-de8e-479b-b25d-47c5ae7e1173
-- statement:
--   Suppose we have $ 2n$ integers between $ - n$ and $ n$ whose sum equals one (Where $ n$ is a natural number bigger than one). Prove that the sum of a subset of these $ 2n$ integers equals zero.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66834 (n : ℕ) (hn : 1 < n) (A : Finset ℤ) (hA : A.card = 2 * n) (hA' : ∀ a ∈ A, -n ≤ a ∧ a ≤ n) (hA'' : ∑ x in A, x = 1) : ∃ B ⊆ A, ∑ x in B, x = 0   :=  by sorry
