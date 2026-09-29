-- Prove2me | solution 1 for lean_workbook_plus_24205
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:45.674632+00:00
-- url     : https://prove2.me/submissions/8ae6c086-0ef8-4ba6-9745-988250f4c93a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (n : ℕ) : (n * (n + 1) * (2 * n + 1) / 6) ≤ 2003 → n ≤ 17 := by
  intro h
  by_contra hn
  have hn : 18 ≤ n := by omega
  have hp : 18*19*37 ≤ n*(n+1)*(2*n+1) := Nat.mul_le_mul (Nat.mul_le_mul hn (by omega)) (by omega)
  omega
