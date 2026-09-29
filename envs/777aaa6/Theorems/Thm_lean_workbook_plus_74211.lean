-- Prove2me | Theorems.Thm_lean_workbook_plus_74211
-- name    : lean_workbook_plus_74211
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/48a5b93e-10a9-4fae-82ae-4e4b9cc6ec1e
-- statement:
--   Let $a_i,1\le i\le n$ be non-negetive real numbers. Let $S$ denote their sum. Prove that $\prod_{k=1}^n (1+a_k)\ge 1+S$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74211 (n : ℕ) (a : ℕ → NNReal) : ∏ k in Finset.range n, (1 + a k) ≥ 1 + ∑ k in Finset.range n, a k   :=  by sorry
