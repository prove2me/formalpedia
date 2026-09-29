-- Prove2me | Theorems.Thm_lean_workbook_plus_55480
-- name    : lean_workbook_plus_55480
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ca4e12a0-1fbd-4af3-8c22-cdb4639c0ff7
-- statement:
--   Find a universal formula for $\sum_{k=1}^n k^j$ as a polynomial in $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55480 (j : ℕ) : ∃ p : ℕ → ℕ, ∀ n : ℕ, ∑ k in Finset.Icc 1 n, k ^ j = p n   :=  by sorry
