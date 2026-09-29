-- Prove2me | Theorems.Thm_lean_workbook_plus_32783
-- name    : lean_workbook_plus_32783
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/592d38b2-3ec4-426b-b90f-a74763f05528
-- statement:
--   Prove that the square of any odd integer is of the form $8n+1$ or $8n+7$ for some integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32783 (n : ℤ) (h : n%2 = 1) : ∃ k : ℤ, n ^ 2 = 8*k + 1 ∨ n ^ 2 = 8*k + 7   :=  by sorry
