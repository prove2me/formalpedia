-- Prove2me | Theorems.Thm_lean_workbook_plus_77047
-- name    : lean_workbook_plus_77047
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6c984c3e-4b02-453a-82a7-9f19f92b0df2
-- statement:
--   Prove that there exist infinitely many natural numbers like $n$ such that: $n|1^n+2^n+...+k^n$, where $k>1$ is a natural number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77047 (k : ℕ) (h : k > 1) : ∃ n : ℕ, n ∣ ∑ i in Finset.range k, i ^ n   :=  by sorry
