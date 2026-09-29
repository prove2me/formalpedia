-- Prove2me | Theorems.Thm_lean_workbook_plus_7449
-- name    : lean_workbook_plus_7449
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/cb883ea5-4846-4c0a-b031-0fadd0444964
-- statement:
--   If $ P=1*2*3...*n$ and $ S=1+2+3+...+n$ , show that when n is odd, S will always divide P, but not necessarily when n is even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7449 (n : ℕ) (hn : n > 0) (h : n % 2 = 1) : (∑ i in Finset.range n, i) ∣ (∏ i in Finset.range n, i)   :=  by sorry
