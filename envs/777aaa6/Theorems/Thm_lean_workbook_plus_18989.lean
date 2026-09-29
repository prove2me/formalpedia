-- Prove2me | Theorems.Thm_lean_workbook_plus_18989
-- name    : lean_workbook_plus_18989
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/457bcf6b-18f3-4787-a7d8-5737e5ecf2e1
-- statement:
--   Prove that for every positive integer $n$, there exists a number written in base 10 with $n$ digits, all of which are 1 or 2, that is divisible by $2^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18989 (n : ℕ) : ∃ m : ℕ, (m % 2 ^ n = 0 ∧ (∀ i ∈ Nat.digits 10 m, i = 1 ∨ i = 2))   :=  by sorry
