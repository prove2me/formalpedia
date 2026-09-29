-- Prove2me | solution 1 for lean_workbook_plus_36696
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:27.270627+00:00
-- url     : https://prove2.me/submissions/2979a90d-5bc8-4a6d-846f-98530367bbd2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n ≥ 2, 6 ∣ n * (n + 1) * (n + 2) := by
  intro n hn
  have hm : n%6<6 := Nat.mod_lt _ (by decide)
  interval_cases h : n%6 <;> norm_num [Nat.dvd_iff_mod_eq_zero,Nat.mul_mod,Nat.add_mod,h]
