-- Prove2me | Theorems.Thm_lean_workbook_plus_36394
-- name    : lean_workbook_plus_36394
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/1db4af3e-8a33-46ff-8b42-9286e8a69fa7
-- statement:
--   Find the number of possible values of $n$ with $1<n<1000$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36394 {n:ℕ | 1<n ∧ n<1000} = {n:ℕ | n ∈ Finset.Icc 2 999}   :=  by sorry
