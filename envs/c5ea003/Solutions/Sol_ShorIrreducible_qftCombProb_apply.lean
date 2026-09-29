-- Prove2me | solution 1 for ShorIrreducible.qftCombProb_apply
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:51:28.338685+00:00
-- url     : https://prove2.me/submissions/4c249e49-55d5-4395-8f73-8ad72703b2c1

-- Sol generated from Novelty/ShorQFTOutput.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutput
import Theorems.Thm_ShorIrreducible_combDFT_eq

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





/-- All surviving output amplitudes have the same modulus: the QFT output of a
comb is *flat*. -/
theorem norm_combDFT {r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
    ‖combDFT r m j y‖ = if m ∣ y then (m : ℝ) else 0 := by
  have hQ : r * m ≠ 0 := Nat.mul_ne_zero hr hm
  have hunit : ‖zeta (r * m) ^ (j * y)‖ = 1 := by
    rw [norm_pow, (isPrimitiveRoot_zeta hQ).norm'_eq_one hQ, one_pow]
  rw [combDFT_eq hr hm]
  by_cases hdvd : m ∣ y
  · rw [if_pos hdvd, if_pos hdvd, norm_mul, hunit, mul_one, Complex.norm_natCast]
  · rw [if_neg hdvd, if_neg hdvd, norm_zero]

/-! ## The output distribution of Shor's algorithm -/





/-! ## Total-variation failure of any small-support sampler -/








open ShorIrreducible in
theorem solution{r m j y : ℕ} (hr : r ≠ 0) (hm : m ≠ 0) :
    ((Real.sqrt ((r : ℝ) * m * m))⁻¹ * ‖combDFT r m j y‖) ^ 2 = qftCombProb r m y := by
  have hrpos : (0 : ℝ) < r := by
    exact_mod_cast Nat.pos_of_ne_zero hr
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hprod : (0 : ℝ) < (r : ℝ) * m * m := by positivity
  rw [norm_combDFT hr hm, qftCombProb]
  by_cases hdvd : m ∣ y
  · rw [if_pos hdvd, if_pos hdvd, mul_pow, inv_pow, Real.sq_sqrt hprod.le]
    field_simp
  · rw [if_neg hdvd, if_neg hdvd, mul_zero]
    ring
