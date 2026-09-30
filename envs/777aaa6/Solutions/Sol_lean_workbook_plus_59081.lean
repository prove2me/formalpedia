-- Prove2me | solution 1 for lean_workbook_plus_59081
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:03:52.318612+00:00
-- url     : https://prove2.me/submissions/6fc55575-ec15-4d04-b4d5-9c060f983483

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 0 < n) : 6 ∣ 7^n - 1 := by
  have h : 7 ^ n ≡ 1 [MOD 6] := by
    have h7 : 7 ≡ 1 [MOD 6] := by decide
    simpa using h7.pow n
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm
