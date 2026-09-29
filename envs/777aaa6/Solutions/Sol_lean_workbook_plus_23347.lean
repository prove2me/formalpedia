-- Prove2me | solution 1 for lean_workbook_plus_23347
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:28.713977+00:00
-- url     : https://prove2.me/submissions/779ed002-3bf5-4856-a87c-934f5797598a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℕ) (h1 : Nat.gcd a b = 13) (h2 : a * b = 897) : Nat.lcm a b = 69 := by
  have h := Nat.gcd_mul_lcm a b
  rw [h1,h2] at h
  omega
