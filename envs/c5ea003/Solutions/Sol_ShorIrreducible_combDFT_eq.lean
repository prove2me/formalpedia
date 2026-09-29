-- Prove2me | solution 1 for ShorIrreducible.combDFT_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:16:51.402185+00:00
-- url     : https://prove2.me/submissions/64f29e0e-105e-4ba9-b73a-7f2501b6b37e

-- Sol generated from Novelty/ShorQFTOutput.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutput

/-! # The QFT output of the comb: exactly `r` flat peaks, and why truncation fails

This file computes the *output* of the quantum Fourier transform on the periodic
comb `[x ≡ x₀ mod r]` of a register of size `Q = r * m`, and derives the
sampling-level obstruction to any classical emulation that keeps only
polynomially many amplitudes.

Main results:

* `combDFT_eq` : the Fourier sum of the comb,
  `∑_{t<m} ζ_Q^{(j + r t) y} = m ζ_Q^{j y}` if `m ∣ y` and `0` otherwise:
  the output is supported on the `r` multiples of `m = Q / r` and nowhere else;
* `norm_combDFT` : all `r` surviving amplitudes have the *same* modulus `m` —
  the output comb is flat, not "nearly a single basis state";
* `qftCombProb_apply` and `sum_qftCombProb` : the measured output distribution
  is uniform on those `r` frequencies;
* `tvDist_ge_sum_sub` and `tvDist_qftComb_ge` : **any** classical sampler whose
  output distribution is supported on a set `S` differs from the ideal Shor
  output distribution in total variation by at least `1 - |S| / r`; with
  `2 * |S| ≤ r` the distance is at least `1/2`
  (`tvDist_qftComb_ge_half`).  A truncated emulation fails catastrophically
  rather than approximately.
-/

open Finset
open scoped Real

open ShorIrreducible

/-! ## The Fourier transform of a comb -/


lemma isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma zeta_pow_eq_one {n : ℕ} (hn : n ≠ 0) : zeta n ^ n = 1 :=
  (isPrimitiveRoot_zeta hn).pow_eq_one

/-- Raising the `Q`-th root of unity to the power `r` gives the `m`-th root,
where `Q = r * m`. -/
lemma zeta_pow_block {r m : ℕ} (hr : r ≠ 0) : zeta (r * m) ^ r = zeta m := by
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  push_cast
  field_simp




/-! ## The output distribution of Shor's algorithm -/





/-! ## Total-variation failure of any small-support sampler -/








open ShorIrreducible in
theorem solution{r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
    combDFT r m j y = if m ∣ y then (m : ℂ) * zeta (r * m) ^ (j * y) else 0 := by
  have hsplit : ∀ t ∈ Finset.range m,
      zeta (r * m) ^ ((j + r * t) * y) = zeta (r * m) ^ (j * y) * (zeta m ^ y) ^ t := by
    intro t _
    rw [← zeta_pow_block (m := m) hr, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [combDFT, Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  by_cases hdvd : m ∣ y
  · have hone : zeta m ^ y = 1 := by
      obtain ⟨k, rfl⟩ := hdvd
      rw [pow_mul, zeta_pow_eq_one hm, one_pow]
    rw [hone, if_pos hdvd]
    simp [mul_comm]
  · have hne : zeta m ^ y ≠ 1 := fun hcon =>
      hdvd (((isPrimitiveRoot_zeta hm).pow_eq_one_iff_dvd y).mp hcon)
    have hgeom : (∑ t ∈ Finset.range m, (zeta m ^ y) ^ t) = 0 := by
      have hmul := geom_sum_mul (x := zeta m ^ y) (n := m)
      have hzero : (zeta m ^ y) ^ m - 1 = 0 := by
        rw [← pow_mul, mul_comm y m, pow_mul, zeta_pow_eq_one hm, one_pow, sub_self]
      rw [hzero] at hmul
      rcases mul_eq_zero.mp hmul with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    rw [hgeom, if_neg hdvd, mul_zero]
