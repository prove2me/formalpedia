-- Prove2me | Theorems.Thm_lean_workbook_plus_10162
-- name    : lean_workbook_plus_10162
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/80f1e868-23c7-4ec9-a6e6-663148031425
-- statement:
--   Prove the formula for the sum of the first $n$ squares, $1^2 + 2^2 + ... + n^2 = n(n+1)(2n+1)/6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10162 : ∀ n, ∑ i in Finset.range (n+1), i^2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
