-- Prove2me | solution 1 for ShorIrreducible.tvDist_ge_sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:51:30.610987+00:00
-- url     : https://prove2.me/submissions/3717816d-b1f0-4c6c-bae8-e55143b52289

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








/-! ## The output distribution of Shor's algorithm -/





/-! ## Total-variation failure of any small-support sampler -/








open ShorIrreducible in
theorem solution{ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι → ℝ}
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (A : Finset ι) :
    ∑ i ∈ A, (p i - q i) ≤ tvDist p q := by
  classical
  have hzero : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hq, sub_self]
  have hsplit : ∑ i ∈ A, (p i - q i) + ∑ i ∈ Aᶜ, (p i - q i) = 0 := by
    rw [Finset.sum_add_sum_compl A (fun i => p i - q i)]
    exact hzero
  have h1 : ∑ i ∈ A, (p i - q i) ≤ ∑ i ∈ A, |p i - q i| :=
    Finset.sum_le_sum fun i _ => le_abs_self _
  have h2 : -∑ i ∈ Aᶜ, (p i - q i) ≤ ∑ i ∈ Aᶜ, |p i - q i| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => neg_le_abs _
  have h3 : ∑ i ∈ A, |p i - q i| + ∑ i ∈ Aᶜ, |p i - q i| = ∑ i, |p i - q i| :=
    Finset.sum_add_sum_compl A _
  rw [tvDist]
  linarith
