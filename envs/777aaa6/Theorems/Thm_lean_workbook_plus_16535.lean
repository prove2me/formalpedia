-- Prove2me | Theorems.Thm_lean_workbook_plus_16535
-- name    : lean_workbook_plus_16535
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/2a546fa2-f8e4-4cf1-9ca8-b3adeddaa64d
-- statement:
--   Prove that for all $n$ , $2^n$ has a multiple having all non-zero digits (in base $10$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16535 (n : ℕ) : ∃ m : ℕ, (2 ^ n)∣m ∧ (Nat.digits 10 m).all (· ≠ 0)   :=  by sorry
