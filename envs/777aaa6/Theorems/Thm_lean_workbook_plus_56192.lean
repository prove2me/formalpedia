-- Prove2me | Theorems.Thm_lean_workbook_plus_56192
-- name    : lean_workbook_plus_56192
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/cd92cd59-9e5a-4bf0-a1b6-6c7e350a37a3
-- statement:
--   Prove that $1^{3}+3^{3}+5^{3}+\ldots+{(2n - 1)}^{3}= n^{2}(2n^{2}- 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56192 : ∀ n, ∑ k in Finset.range n, (2 * k - 1) ^ 3 = n ^ 2 * (2 * n ^ 2 - 1)   :=  by sorry
