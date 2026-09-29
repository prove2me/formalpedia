-- Prove2me | solution 1 for lean_workbook_plus_11632
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:23.965114+00:00
-- url     : https://prove2.me/submissions/4f0312c3-cd7d-4961-97eb-64826d621438

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (h : n ≥ 2) : (n + 1).choose 2 = n * (n + 1) / 2 := by
  rw [Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm n (n+1)]
