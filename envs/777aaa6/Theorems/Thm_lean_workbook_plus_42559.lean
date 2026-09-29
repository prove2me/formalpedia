-- Prove2me | Theorems.Thm_lean_workbook_plus_42559
-- name    : lean_workbook_plus_42559
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/13ac8aa9-f689-4cd6-a76d-f3b1c7f896f6
-- statement:
--   Find the limit of the sequence defined by $a_n = \frac{1}{2} + \frac{1}{4} + \frac{1}{8} + \ldots + \frac{1}{2^n}$ as $n$ approaches infinity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42559 (n : ℕ) : ∃ l, ∑ i in Finset.range n, (1 / (2 ^ i)) = l   :=  by sorry
