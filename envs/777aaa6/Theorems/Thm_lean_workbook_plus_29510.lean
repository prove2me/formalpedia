-- Prove2me | Theorems.Thm_lean_workbook_plus_29510
-- name    : lean_workbook_plus_29510
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/98ef79dd-03fc-403a-b2ee-a6bb81187629
-- statement:
--   Given $1 + 2 + \cdots + 2^n = 2^{n + 1} - 1$, how can you find $(1 + 2 + \cdots + 2^n) - 1$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29510 : ∀ n, (∑ i in Finset.range (n + 1), 2 ^ i) - 1 = 2 ^ n - 1   :=  by sorry
