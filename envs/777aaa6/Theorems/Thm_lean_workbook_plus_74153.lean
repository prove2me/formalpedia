-- Prove2me | Theorems.Thm_lean_workbook_plus_74153
-- name    : lean_workbook_plus_74153
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/83d6dadd-3b79-4220-a3eb-f90685383853
-- statement:
--   What is the value of $\sum_{i=1}^{100} i$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74153 (n : ℕ) : ∑ i in Finset.range 101, i = 5050   :=  by sorry
