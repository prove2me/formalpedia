-- Prove2me | solution 1 for lean_workbook_plus_36283
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:55:02.801095+00:00
-- url     : https://prove2.me/submissions/ee641a22-6d4b-4a0a-93b6-a778fc68710e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ n : ℕ, 3 ∣ n ^ 3 - n + 3 := by
  intro n
  have hc : n^3 ≡ n [MOD 3] := by
    unfold Nat.ModEq
    rw [Nat.pow_mod]
    have hlt := Nat.mod_lt n (by decide : 0 < 3)
    interval_cases h : n % 3 <;> norm_num [h]
  have hle : n ≤ n^3 := Nat.le_self_pow (by decide) n
  exact dvd_add ((Nat.modEq_iff_dvd' hle).mp hc.symm) (dvd_refl 3)
