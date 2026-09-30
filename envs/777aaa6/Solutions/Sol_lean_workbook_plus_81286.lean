-- Prove2me | solution 1 for lean_workbook_plus_81286
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:14.561848+00:00
-- url     : https://prove2.me/submissions/91046f60-de7c-4c6d-b203-ec0054037e4a

import Mathlib

theorem solution (n : ℕ) : ¬∃ k : ℕ, n^2 < k^2 ∧ k^2 < (n + 1)^2 := by
  rintro ⟨k, hlow, hhigh⟩
  have hnk := (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hlow
  have hkn := (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hhigh
  omega
