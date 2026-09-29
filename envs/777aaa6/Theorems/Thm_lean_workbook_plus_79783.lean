-- Prove2me | Theorems.Thm_lean_workbook_plus_79783
-- name    : lean_workbook_plus_79783
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/17215248-4812-4c6f-87a3-e5a341eaa0b3
-- statement:
--   Given the geometric sequence $S = \frac{1}{2} + \frac{1}{4} + \frac{1}{8} + \ldots$, show that $S = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79783 (n : ℕ) (hn: n > 0) : (∑ k in Finset.range n, (1 / (2^k))) = 1   :=  by sorry
