-- Prove2me | solution 2 for lean_workbook_plus_10412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:25.045852+00:00
-- url     : https://prove2.me/submissions/61b1089f-8d7f-4cf0-acb7-54d6604e128d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℕ) (h : 1 ≤ k) : 2 ^ (k - 1) ≥ k := by
  have hp : k-1 < 2^(k-1) := Nat.lt_two_pow_self
  omega
