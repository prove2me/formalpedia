-- Prove2me | Theorems.Thm_lean_workbook_plus_62482
-- name    : lean_workbook_plus_62482
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9c19c862-1602-4eb3-a784-bc44966c100a
-- statement:
--   Given $k \ge 4$, prove that $\sum_{i = 1}^k i! > k^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62482 : ∀ k ≥ 4, ∑ i in Finset.Icc 1 k, i! > k^2   :=  by sorry
