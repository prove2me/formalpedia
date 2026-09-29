-- Prove2me | solution 1 for lean_workbook_plus_15514
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:56:57.655315+00:00
-- url     : https://prove2.me/submissions/7cb0821f-ab8e-4d4f-969b-ac3065b14c0e

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : 3 ∣ n ^ 3 - n + 3 := by
  have hle : n ≤ n ^ 3 := by
    by_cases h : n = 0
    · simp [h]
    · exact le_self_pow (by omega : 1 ≤ n) (by decide : (3 : ℕ) ≠ 0)
  have hd : (3 : ℤ) ∣ (n : ℤ) ^ 3 - n := Int.prime_dvd_pow_self_sub (by norm_num : Nat.Prime 3) n
  have hd' : 3 ∣ n ^ 3 - n := by
    exact_mod_cast hd
  exact dvd_add hd' (dvd_refl 3)
