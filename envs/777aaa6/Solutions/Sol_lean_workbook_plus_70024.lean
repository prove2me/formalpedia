-- Prove2me | solution 1 for lean_workbook_plus_70024
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:14.649707+00:00
-- url     : https://prove2.me/submissions/d88557a0-7ea2-460c-8edc-413048862800

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℕ) (h₁ : 1 ≤ b) (h₂ : b ≤ a) :  (b + 1) * (b + 2) * (a - b + 1) * (a - b + 2) ≥ 2 * (a + 1) * (a + 2) := by
  set t := a - b
  have he : a = b + t := by dsimp [t]; omega
  change (b+1)*(b+2)*(t+1)*(t+2) ≥ 2*(a+1)*(a+2)
  rw [he]
  nlinarith [Nat.zero_le (b * t * (b * t + 3 * b + 3 * t + 5))]
