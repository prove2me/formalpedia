-- Prove2me | Theorems.Thm_lean_workbook_plus_39282
-- name    : lean_workbook_plus_39282
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/93cb77e5-d453-4e4e-805b-4d631774e0af
-- statement:
--   Prove that for any natural number $m$, there exists a natural number $n$ such that $n$ is divisible by $m$ and all digits of $n$ are 0 and 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39282 (m : ℕ) : ∃ n : ℕ, n % m = 0 ∧ (∀ i ∈ Nat.digits 10 n, i = 0 ∨ i = 1)   :=  by sorry
