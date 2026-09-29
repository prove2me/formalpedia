-- Prove2me | Theorems.Thm_lean_workbook_plus_68400
-- name    : lean_workbook_plus_68400
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c59b673c-2206-48bd-8424-ce06e211e7f8
-- statement:
--   Two different numbers are selected at random from $( 1, 2, 3, 4, 5)$ and multiplied together. What is the probability that the product is even?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68400 ∃ a b, a ≠ b ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5 ∧ (a * b) % 2 = 0   :=  by sorry
