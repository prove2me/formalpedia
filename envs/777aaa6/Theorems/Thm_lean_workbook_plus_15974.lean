-- Prove2me | Theorems.Thm_lean_workbook_plus_15974
-- name    : lean_workbook_plus_15974
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6c5d801d-4be6-4955-a02b-587bb5060ba1
-- statement:
--   Prove that $\sum_{k=1}^n(k-1)=\sum_{k=0}^{n-1}k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15974 (n : ℕ) :
  ∑ k in Finset.range n, (k - 1) = ∑ k in Finset.range (n - 1), k   :=  by sorry
