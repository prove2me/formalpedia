-- Prove2me | Theorems.Thm_lean_workbook_plus_79143
-- name    : lean_workbook_plus_79143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/fcd0836b-359a-4ffa-9102-b6a3584d2ba5
-- statement:
--   if it is positive integers then $0 < k < 11$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79143 (k : ℤ) : 0 < k ∧ k < 11 ↔ k ∈ Finset.Ioo 0 11   :=  by sorry
