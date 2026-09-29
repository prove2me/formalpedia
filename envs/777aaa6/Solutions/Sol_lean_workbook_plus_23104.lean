-- Prove2me | solution 1 for lean_workbook_plus_23104
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:07.687274+00:00
-- url     : https://prove2.me/submissions/aa6b0953-98bd-433f-b9a8-07a2448fb508

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℕ) (h₁ : c ∣ b) (h₂ : a ∣ b / c) : a ∣ b := by
  exact dvd_trans h₂ (Nat.div_dvd_of_dvd h₁)
