-- Prove2me | Theorems.Thm_lean_workbook_plus_35681
-- name    : lean_workbook_plus_35681
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a2e36d88-a2b7-4bd5-a366-2f2152c8fc07
-- statement:
--   Given $T = 1 + 2 + ... + n$, prove that $S = 2 + 4 + ... + 2n = 2T$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35681 (n : ℕ) : ∑ i in Finset.range n, 2 * i = 2 * ∑ i in Finset.range n, i   :=  by sorry
