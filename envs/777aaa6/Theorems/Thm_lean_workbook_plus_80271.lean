-- Prove2me | Theorems.Thm_lean_workbook_plus_80271
-- name    : lean_workbook_plus_80271
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b70970a0-a900-49ab-875d-4b740ab1b15f
-- statement:
--   Prove that $\sum_{y=0}^{n}\binom{m+y}{y} =\binom{n+m+1}{n}$ where $m,n$ are nonnegative integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80271 (m n : ℕ) : ∑ y in Finset.range (n+1), choose (m+y) y = choose (n+m+1) n   :=  by sorry
