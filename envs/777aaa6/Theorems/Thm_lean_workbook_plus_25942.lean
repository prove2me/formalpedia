-- Prove2me | Theorems.Thm_lean_workbook_plus_25942
-- name    : lean_workbook_plus_25942
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6b2c637c-aa6d-4193-b002-ae98238795c2
-- statement:
--   Erdos-Ginzburg-Ziv Theorem: For any set of $2n-1$ positive integers, there exists $n$ positive integers in the set such that the sum of these positive integers is divisible by $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25942 (n : ℕ) (A : Finset ℕ) (hA : A.card = 2 * n - 1) :
    ∃ B : Finset ℕ, B ⊆ A ∧ n ∣ B.sum (fun x ↦ x)   :=  by sorry
