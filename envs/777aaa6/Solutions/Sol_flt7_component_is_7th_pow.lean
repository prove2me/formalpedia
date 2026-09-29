-- Prove2me | solution 1 for flt7_component_is_7th_pow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:21:00.601211+00:00
-- url     : https://prove2.me/submissions/b931f542-fb8c-4a4a-89fa-b330bb4d84cd

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

theorem solution (A B N : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hcop : Nat.Coprime A B) (hprod : A * B = N^7) :
    ∃ d : ℕ, A = d^7 := by
  have hcop_int : IsCoprime (A:ℤ) (B:ℤ) := hcop.isCoprime
  have hprod_int : (A:ℤ) * (B:ℤ) = (N:ℤ)^7 := by exact_mod_cast hprod
  obtain ⟨d, hd⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop_int (⟨3, rfl⟩ : Odd 7) hprod_int
  have h7pos : (0:ℤ) < d^7 := hd.symm ▸ (by exact_mod_cast hA)
  have hd_pos : 0 < d := by
    rcases lt_or_ge 0 d with hd | hd
    · exact hd
    · have h6 : 0 ≤ d^6 := by rw [show d^6 = (d^3)^2 from by ring]; exact sq_nonneg _
      have : d^7 ≤ 0 := by nlinarith [show d * d^6 = d^7 from by ring]
      linarith
  use d.toNat
  have hd_nat : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd_pos.le
  have : (d.toNat^7 : ℤ) = (A : ℤ) := by push_cast [hd_nat]; exact hd.symm
  exact_mod_cast this.symm
