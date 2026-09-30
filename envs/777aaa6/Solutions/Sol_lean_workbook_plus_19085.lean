-- Prove2me | solution 1 for lean_workbook_plus_19085
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:30:45.017016+00:00
-- url     : https://prove2.me/submissions/1569230d-0726-4ba5-a1c4-ca3fe53ef66f

import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

theorem cubic_roots_mod_199_iff (x : ℤ) :
    x ^ 3 ≡ 1 [ZMOD 199] ↔ x % 199 = 1 ∨ x % 199 = 92 ∨ x % 199 = 106 := by
  have hp : Prime (199 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  have hgap : (199 : ℤ) ∣ (x ^ 3 - 1) - (x - 1) * (x - 92) * (x - 106) :=
    ⟨x ^ 2 - 50 * x + 49, by ring⟩
  calc
    x ^ 3 ≡ 1 [ZMOD 199] ↔ (199 : ℤ) ∣ x ^ 3 - 1 := by
      rw [Int.modEq_iff_dvd]
      omega
    _ ↔ (199 : ℤ) ∣ (x - 1) * (x - 92) * (x - 106) :=
      dvd_iff_dvd_of_dvd_sub hgap
    _ ↔ ((199 : ℤ) ∣ x - 1 ∨ (199 : ℤ) ∣ x - 92) ∨ (199 : ℤ) ∣ x - 106 := by
      rw [hp.dvd_mul, hp.dvd_mul]
    _ ↔ x % 199 = 1 ∨ x % 199 = 92 ∨ x % 199 = 106 := by omega

theorem solution (x : ℤ) (hx : 2 ≤ x ∧ x ≤ 199) (h : x ^ 3 ≡ 1 [ZMOD 199]) :
    x = 92 ∨ x = 106 := by
  have hr := (cubic_roots_mod_199_iff x).mp h
  omega
