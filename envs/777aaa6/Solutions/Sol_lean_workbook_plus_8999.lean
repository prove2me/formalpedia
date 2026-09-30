-- Prove2me | solution 1 for lean_workbook_plus_8999
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:13:00.58456+00:00
-- url     : https://prove2.me/submissions/9d74f849-92d8-477b-8bd7-0b504022a2b3

import Mathlib.Analysis.Complex.Basic

theorem solution (m : ℕ) (hm1 : 2 < m) (hm2 : Odd m) : ∃ n : ℕ, (2^1989 ∣ m^n - 1) ∧ (∀ k : ℕ, (2^1989 ∣ m^k - 1) → n ≤ k) :=
  ⟨0, by simp, fun k _ => Nat.zero_le k⟩
