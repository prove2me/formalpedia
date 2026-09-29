-- Prove2me | Theorems.Thm_lean_workbook_plus_51685
-- name    : lean_workbook_plus_51685
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/b8673c5b-a95f-4a6d-8cb6-ee71ecf18de9
-- statement:
--   Prove that for any integer $x$, there exists an integer $n$ such that $n \le x < n+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51685 (x : ℤ) : ∃ n, n ≤ x ∧ x < n + 1   :=  by sorry
