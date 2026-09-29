-- Prove2me | solution 1 for lean_workbook_plus_10458
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:35:06.070278+00:00
-- url     : https://prove2.me/submissions/206080b5-c42c-43b0-b0b8-169e797d03e5

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (p : ℕ) (hp : p.Prime) (a b : ℕ) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  exact Nat.Prime.dvd_or_dvd hp hab
