-- Prove2me | Theorems.Thm_lean_workbook_plus_29800
-- name    : lean_workbook_plus_29800
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8fe7edd4-2fee-4b91-8c77-3db8d11e8e34
-- statement:
--   Prove that the square of any odd integer is of the form $8n + 1$ for some integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29800 (k : ℤ) (h : k % 2 = 1) : ∃ n : ℤ, k ^ 2 = 8 * n + 1   :=  by sorry
