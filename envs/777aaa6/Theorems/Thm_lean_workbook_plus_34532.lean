-- Prove2me | Theorems.Thm_lean_workbook_plus_34532
-- name    : lean_workbook_plus_34532
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7bcd74e6-9a7e-4f6b-8a74-597b1977f751
-- statement:
--   Derive the formula $1 + 2 + 3 + \cdots + (n - 1) + n = \frac{n(n + 1)}{2}$ for the sum of the first n natural numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34532 (n : ℕ) : (∑ i in Finset.range (n + 1), i) = n * (n + 1) / 2   :=  by sorry
