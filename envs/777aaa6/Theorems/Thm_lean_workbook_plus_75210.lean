-- Prove2me | Theorems.Thm_lean_workbook_plus_75210
-- name    : lean_workbook_plus_75210
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/fea1d592-b3c7-44c4-a075-25ab21736712
-- statement:
--   Every odd number can be written as $2k+1$ form. So every square of a odd number can be written as $(2k+1)^2=4k^2+4k+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75210 (n : ℤ) (h : n%2 = 1) : ∃ k, n = 2 * k + 1 ∧ n^2 = 4 * k^2 + 4 * k + 1   :=  by sorry
