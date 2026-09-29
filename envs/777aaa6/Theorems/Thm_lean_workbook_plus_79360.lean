-- Prove2me | Theorems.Thm_lean_workbook_plus_79360
-- name    : lean_workbook_plus_79360
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d4d0954b-ba6c-4d5a-85c9-0dd03d9a6165
-- statement:
--   Show that $1 + 2 + 4 + ... + 2^{n-1} = 2^{n}-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79360 : ∀ n : ℕ, ∑ i in Finset.range n, 2 ^ i = 2 ^ n - 1   :=  by sorry
