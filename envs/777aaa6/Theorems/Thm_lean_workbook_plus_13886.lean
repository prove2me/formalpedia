-- Prove2me | Theorems.Thm_lean_workbook_plus_13886
-- name    : lean_workbook_plus_13886
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4ba0f37a-d002-48ac-ba16-ac2302f87f03
-- statement:
--   Let $n$ be a natural number. Prove that there exists a natural number $N$ such that $2^n$ divides $N$ and $N$ does not have any zero digit in base-10 representation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13886 (n : ℕ) : ∃ N : ℕ, 2 ^ n ∣ N ∧ ¬ 0 ∈ Nat.digits 10 N   :=  by sorry
