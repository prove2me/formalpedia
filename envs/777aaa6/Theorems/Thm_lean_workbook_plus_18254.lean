-- Prove2me | Theorems.Thm_lean_workbook_plus_18254
-- name    : lean_workbook_plus_18254
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9a1ef9d1-6354-4899-9d81-f30c4d409eb0
-- statement:
--   The number of subsets of a set with $n$ elements is $2^n$ because each element has $2$ choices, in the subset or not in the subset.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18254 (n : ℕ) : 2 ^ n = Finset.card (Finset.powerset (Finset.range n))   :=  by sorry
