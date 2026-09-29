-- Prove2me | solution 1 for lean_workbook_plus_52700
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:10:20.571159+00:00
-- url     : https://prove2.me/submissions/70688174-363b-454d-a8df-28935a698df5

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a n : ℕ) (h₁ : a > 1) (h₂ : n ≥ 1) : a - 1 ∣ a ^ n - 1 := by
  exact Nat.sub_one_dvd_pow_sub_one a n
