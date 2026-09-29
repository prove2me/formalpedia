-- Prove2me | solution 1 for lean_workbook_plus_24287
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:34:51.712725+00:00
-- url     : https://prove2.me/submissions/82c04d18-19d8-4017-a198-df9191e5d115

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c : ℕ) (hab : Nat.Coprime a b) (hbc : b * c ≠ 0) (h : a ∣ b * c) : a ∣ c := by
  exact Nat.Coprime.dvd_of_dvd_mul_left hab h
