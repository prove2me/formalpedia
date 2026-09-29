-- Prove2me | Theorems.Thm_lean_workbook_plus_62640
-- name    : lean_workbook_plus_62640
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6b66fb60-a805-4263-bb12-fb38df6e8fc0
-- statement:
--   Prove that for every positive integer k there exist positive integer n which has 2 conditions : (i) Each of its digits belongs to the set S={1, 3, 5, 9} (ii) It is divisible to $5^k$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62640 (k : ℕ) : ∃ n : ℕ, (∀ i ∈ (Nat.digits 10 n), i ∈ ({1, 3, 5, 9} : Finset ℕ)) ∧ (5^k ∣ n)   :=  by sorry
