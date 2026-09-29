-- Prove2me | Theorems.Thm_lean_workbook_plus_57408
-- name    : lean_workbook_plus_57408
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/72329907-7d7f-4019-8394-9af7c8a4c367
-- statement:
--   Prove or disprove: $\sum_{k=1}^n \frac{k}{(2n-2k+1)(2n-k+1)} = \sum_{k=1}^n \left[\frac1{2n-2k+1}-\frac1{2n-k+1}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57408 ∀ n, ∑ k in Finset.Icc 1 n, (k / ((2 * n - 2 * k + 1) * (2 * n - k + 1))) = ∑ k in Finset.Icc 1 n, (1 / (2 * n - 2 * k + 1) - 1 / (2 * n - k + 1))   :=  by sorry
