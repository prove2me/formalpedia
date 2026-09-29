-- Prove2me | Theorems.Thm_lean_workbook_plus_47447
-- name    : lean_workbook_plus_47447
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c68d1998-25a7-49be-893b-9bb2c7ea9df2
-- statement:
--   Is the answer $\frac1{60} n (3 n^4 - 15 n^3 + 25 n^2 - 15 n + 2)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47447 ∀ n : ℕ, ∑ k in Finset.range n, (k+1) * (k+2) * (k+3) * (k+4) = n * (3 * n ^ 4 - 15 * n ^ 3 + 25 * n ^ 2 - 15 * n + 2) / 60   :=  by sorry
