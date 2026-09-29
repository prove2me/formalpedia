-- Prove2me | Theorems.Thm_lean_workbook_plus_62543
-- name    : lean_workbook_plus_62543
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/87bd7460-8819-48ea-a9f9-565b1d7ca25a
-- statement:
--   Give an explicit closed form for $\sum_{k=1}^n\frac 1{(3k-2)(2k+1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62543 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, (1 : ℝ) / ((3 * k - 2) * (2 * k + 1)) = n / (2 * n + 1)   :=  by sorry
