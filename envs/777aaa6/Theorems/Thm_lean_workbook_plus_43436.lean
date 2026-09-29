-- Prove2me | Theorems.Thm_lean_workbook_plus_43436
-- name    : lean_workbook_plus_43436
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/376c9984-61dd-4fa7-9f9c-fbe4036ffdf5
-- statement:
--   Prove that any set of cardinality $n$ has $2^n$ subsets.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43436 (n : ℕ) (s : Finset α) (hs : s.card = n) :
  s.powerset.card = 2 ^ n   :=  by sorry
