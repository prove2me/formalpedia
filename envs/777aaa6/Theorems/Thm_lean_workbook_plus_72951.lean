-- Prove2me | Theorems.Thm_lean_workbook_plus_72951
-- name    : lean_workbook_plus_72951
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/87393a64-aa13-4ace-9764-dfd5c2ae6c49
-- statement:
--   for any positive integer n prove that $(2n)! < [n(n+1)]^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72951 : ∀ n : ℕ, (2 * n)! < (n * (n + 1)) ^ n   :=  by sorry
