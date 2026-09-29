-- Prove2me | Theorems.Thm_lean_workbook_plus_40314
-- name    : lean_workbook_plus_40314
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/355762e1-8421-47de-978f-92eb2b92d0f9
-- statement:
--   Prove that for all positive integers $n,$ the sum of the first $n$ positive perfect squares is equal to $\tfrac{n(n+1)(2n+1)}{6}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40314 (n : ℕ) : ∑ i in Finset.range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
