-- Prove2me | Theorems.Thm_lean_workbook_plus_23174
-- name    : lean_workbook_plus_23174
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/bec86f3a-f6f9-4c79-85fd-6b4bd0d1bebb
-- statement:
--   Show that the $n$ th triangular number is given by the formula\n\n$T_{n}=\frac{1}{2}n(n+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23174 (n : ℕ) : ∑ i in Finset.range (n+1), i = n * (n + 1) / 2   :=  by sorry
