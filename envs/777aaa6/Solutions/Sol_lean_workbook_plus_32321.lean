-- Prove2me | solution 1 for lean_workbook_plus_32321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:40.172727+00:00
-- url     : https://prove2.me/submissions/2a14bb28-0b84-4e5e-8f5a-ee054d89b112

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (h : ⌊a⌋ < ⌊b⌋) : a ≤ b := by
  by_contra hn
  have hab : b ≤ a := le_of_lt (lt_of_not_ge hn)
  have hf := Int.floor_mono hab
  omega
