-- Prove2me | Theorems.Thm_lean_workbook_plus_28323
-- name    : lean_workbook_plus_28323
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f4602a87-17db-4fb8-9333-d0c3657c8d03
-- statement:
--   Prove that for any finite $K$, $\sum_{k\in K}{\frac{1}{k(k+1)}}<\sum_{k=1}^{\infty}{\frac{1}{k(k+1)}}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28323 (K : Finset ℕ) :
  ∑ k in K, (1 : ℝ) / (k * (k + 1)) < ∑' k : ℕ, 1 / (k * (k + 1))   :=  by sorry
