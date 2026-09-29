-- Prove2me | Theorems.Thm_lean_workbook_plus_63470
-- name    : lean_workbook_plus_63470
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6a8d8b0f-a82f-4f1a-84d1-6205f2dc4048
-- statement:
--   There are only nine primes less than or equal to $26$ , that are $2,3,5,7,11,13,17,19$ and $23$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63470 {2,3,5,7,11,13,17,19,23} = { p:ℕ | p.Prime ∧ p ≤ 26}   :=  by sorry
