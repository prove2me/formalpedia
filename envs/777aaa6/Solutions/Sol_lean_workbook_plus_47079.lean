-- Prove2me | solution 1 for lean_workbook_plus_47079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:23.031323+00:00
-- url     : https://prove2.me/submissions/ba05f7f8-912a-45ef-b48e-1f52987df39b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x a k : ℕ) : 10 * x + a = 2 * (a * 10 ^ k + x) → 8 * x = a * (2 * 10 ^ k - 1) := by
  intro h
  rw [Nat.mul_sub_left_distrib,mul_one]
  have hp : 0<10^k := by positivity
  have hid : a*(2*10^k)=2*(a*10^k) := by ring
  omega
