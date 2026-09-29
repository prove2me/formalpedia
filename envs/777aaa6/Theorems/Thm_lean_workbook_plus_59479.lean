-- Prove2me | Theorems.Thm_lean_workbook_plus_59479
-- name    : lean_workbook_plus_59479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c9755f77-0051-4599-964c-18f0f63cfa04
-- statement:
--   Given the definitions of even and odd, prove that if $n$ is even, then $n+1$ is odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59479 (n : ℕ) (h : Even n) : Odd (n + 1)   :=  by sorry
