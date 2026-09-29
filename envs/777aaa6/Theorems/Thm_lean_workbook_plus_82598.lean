-- Prove2me | Theorems.Thm_lean_workbook_plus_82598
-- name    : lean_workbook_plus_82598
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/965ab738-c9c6-4fb4-b07f-81f51d198f96
-- statement:
--   Prove that the sum of the first $n$ odd numbers is $n^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82598 (n : ℕ) : ∑ k in Finset.range n, (2 * k + 1) = n^2   :=  by sorry
