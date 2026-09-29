-- Prove2me | Theorems.Thm_lean_workbook_plus_69171
-- name    : lean_workbook_plus_69171
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a56075aa-2866-444d-a743-a51762f4c137
-- statement:
--   Determine with proof whether there exist pairwise relatively prime positive integers $a,b,c >1$ such that $a|2^b+1, b|2^c+1, c|2^a+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69171 (a b c : ℕ) (hab : a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1) (hgcd : Nat.gcd a b = 1 ∧ Nat.gcd b c = 1 ∧ Nat.gcd c a = 1) (hdiv : a ∣ 2 ^ b + 1 ∧ b ∣ 2 ^ c + 1 ∧ c ∣ 2 ^ a + 1) : a ∣ 2 ^ b + 1 ∧ b ∣ 2 ^ c + 1 ∧ c ∣ 2 ^ a + 1   :=  by sorry
