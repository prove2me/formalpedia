-- Prove2me | Theorems.Thm_lean_workbook_plus_40989
-- name    : lean_workbook_plus_40989
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/89476afe-2a21-4aa3-b58f-a206f7afc090
-- statement:
--   Find the expression for the sum of the finite version of the series $\sum\limits_{k=1}^N {k^a b^k}$ with $a>0, a \in R$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40989 (a : ℝ) (b : ℝ) (N : ℕ) : ∑ k in Finset.Icc 1 N, (k^a * b^k) = (∑ k in Finset.Icc 1 N, (k^a * b^k))   :=  by sorry
