-- Prove2me | Theorems.Thm_lean_workbook_plus_44806
-- name    : lean_workbook_plus_44806
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1ddde9d6-a846-4b1f-96e0-5354900fd133
-- statement:
--   For all positive integers $n$ , show that there exists an $n$ -digit multiple of $2^n$ consisting of only of $8$ s and $9$ s.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44806 (n : ℕ) (hn : 1 ≤ n) : ∃ m, (2^n ∣ m) ∧ (Nat.digits 10 m).all (· ∈ ({8, 9} : Finset ℕ))   :=  by sorry
