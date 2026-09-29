-- Prove2me | Theorems.Thm_lean_workbook_plus_6008
-- name    : lean_workbook_plus_6008
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/258c5a3a-8554-4ef9-847c-c1abcab6ace4
-- statement:
--   How many numbers between $ 1$ and $ 2010$ (exclusive) have no factor in common with $ 2010$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6008 {n:ℕ | 1<= n ∧ n <= 2010 ∧ Nat.gcd n 2010 = 1} = {n:ℕ | 1<= n ∧ n <= 2010 ∧ Nat.gcd n 2 = 1 ∧ Nat.gcd n 3 = 1 ∧ Nat.gcd n 5 = 1 ∧ Nat.gcd n 67 = 1}   :=  by sorry
