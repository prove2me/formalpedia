-- Prove2me | Theorems.Thm_lean_workbook_plus_56297
-- name    : lean_workbook_plus_56297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/78078cc8-bbfd-4c67-b5fc-20de90adf6e4
-- statement:
--   Use the division algorithm to show that every odd integer is either of the form $4k + 1$ or $4k + 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56297 (n : ℤ) (h : n%2 = 1) : ∃ k : ℤ, n = 4*k + 1 ∨ n = 4*k + 3   :=  by sorry
