-- Prove2me | Theorems.Thm_lean_workbook_plus_71646
-- name    : lean_workbook_plus_71646
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c6c081f5-f72f-4828-8338-9cab69f153e1
-- statement:
--   $ \sum_{n = 1}^{98} n(n + 1) = \sum_{1}^{98} (n^{2} + n)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71646 (n : ℕ) : ∑ n in Finset.Icc 1 98, n * (n + 1) = ∑ n in Finset.Icc 1 98, (n ^ 2 + n)   :=  by sorry
