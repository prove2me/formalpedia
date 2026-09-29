-- Prove2me | Theorems.Thm_lean_workbook_plus_22002
-- name    : lean_workbook_plus_22002
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f84f3e7c-3da4-46c5-91c4-93103757cecc
-- statement:
--   Find the number of integers less than or equal to $n$ that are relatively prime to $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22002 (n : ℕ) : ∑ k in Finset.filter (λ x => Nat.gcd x n = 1) (Finset.range n), 1 = Nat.totient n   :=  by sorry
