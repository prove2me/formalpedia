-- Prove2me | solution 1 for CollatzSpectral.peak_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:18:16.273122+00:00
-- url     : https://prove2.me/submissions/77974cfa-a73c-412d-ab8e-41a4f943325c

-- Sol generated from Novelty/CollatzSpectralNormalized.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized
import Theorems.Thm_CollatzSpectral_norm_limitAmp
import Theorems.Thm_CollatzSpectral_tendsto_F_div

/-!
# Normalized spectral transforms of the `an + 1` maps

This file develops a *corrected* spectral theory for the one-step "Collatz phase"
exponential sums.  Fix an odd multiplier `a` and consider the accelerated map

`step a n = n / 2` if `n` is even, `step a n = a * n + 1` if `n` is odd,

and the *phase ratio* `ratio a n = step a n / n`.  The cutoff transform is

`F a ω N = ∑_{n = 1}^{N} e(ω · ratio a n)`,  `e(x) = exp(2πi x)`.

The previous cycle attempted a *pointwise* smallness statement for `F a ω N`
valid for all irrational `ω`.  That is impossible: `ratio` takes only the value
`1/2` on the even branch and values `a + 1/n → a` on the odd branch, so the
normalized transform converges to an explicit trigonometric amplitude which is
close to `1` for `ω` near an integer resonance.  Here we prove exactly that.

## Main results

* `ratio_even`, `ratio_odd` — the even/odd splitting of the phase: constant `1/2`
  on evens, `a + 1/n` on odds.
* `F_even_odd_split` — the exact finite decomposition of `F a ω N` into a purely
  constant even contribution and a modulated odd contribution.
* `tendsto_F_div` — **the normalization theorem**:
  `F a ω N / N → (e(ω/2) + e(aω))/2 =: limitAmp a ω` for every real `ω`.
* `norm_limitAmp` — `‖limitAmp a ω‖ = |cos(π (a - 1/2) ω)|`.
* `limitAmp_eq_zero_iff` — the resonance ("spectral gap") set is exactly
  `{ω : (2a - 1) ω is an odd integer}`.
* `tendsto_F_div_of_resonance` — genuine `o(N)` cancellation at resonances.
* `eventually_norm_F_ge` — no cancellation off resonance: `‖F a ω N‖ ≥ c N`.
* `peak_near_zero` — continuity near frequency `0` forces `‖F a ω N‖ ≳ N/4`,
  which refutes any global pointwise decay statement.
* `discriminator_one_fifth` — at `ω = 1/5` the `3n+1` map has a spectral gap
  while the `5n+1` and `7n+1` maps do not: a genuine arithmetic discriminator.
* `meanSquare_limitAmp` — the mean square of the amplitude over a full period
  equals `1/2` for **every** `a`: `L²`-averaging cannot discriminate, only the
  location of the resonance set can.
-/

open CollatzSpectral

open Filter Complex
open scoped Real Topology

/-! ## The character `e(x) = exp(2π i x)` -/








/-! ## The maps and their phase ratios -/





/-! ## The cutoff transform -/







/-! ## Convergence of the normalized transform -/







/-! ## The amplitude: modulus, resonances, and the discriminator -/




/-- **No cancellation off resonance**: away from the resonance set the transform
has full linear size along the whole sequence. -/
theorem eventually_norm_F_ge (a : ℕ) (ω : ℝ) (h : limitAmp a ω ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, (‖limitAmp a ω‖ / 2) * N ≤ ‖F a ω N‖ := by
  have hlim := (tendsto_F_div a ω).norm
  have hpos : 0 < ‖limitAmp a ω‖ := norm_pos_iff.mpr h
  have hlt : ‖limitAmp a ω‖ / 2 < ‖limitAmp a ω‖ := by linarith
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ‖limitAmp a ω‖ / 2 ≤ ‖F a ω N / (N : ℂ)‖ :=
    hlim.eventually_const_le hlt
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  rw [norm_div, Complex.norm_natCast, le_div_iff₀ hN0] at hN
  linarith [hN]


/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/



open CollatzSpectral in
theorem solution(a : ℕ) (ω : ℝ) (hω : |(2 * (a : ℝ) - 1) * ω| ≤ 2 / 3) :
    ∀ᶠ N : ℕ in Filter.atTop, (1 / 4 : ℝ) * N ≤ ‖F a ω N‖ := by
  set t : ℝ := ((a : ℝ) - 1 / 2) * ω with ht
  have hpi : |Real.pi * t| ≤ Real.pi / 3 := by
    have h1 : |t| ≤ 1 / 3 := by
      have : |(2 * (a : ℝ) - 1) * ω| = 2 * |t| := by
        rw [ht, abs_mul, abs_mul]
        rw [show (2 * (a : ℝ) - 1) = 2 * ((a : ℝ) - 1 / 2) by ring, abs_mul]
        simp
        ring
      linarith [this ▸ hω]
    calc |Real.pi * t| = Real.pi * |t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi * (1 / 3) := by nlinarith [Real.pi_pos]
      _ = Real.pi / 3 := by ring
  have hcos : (1 : ℝ) / 2 ≤ Real.cos (Real.pi * t) := by
    have h2 : Real.cos (Real.pi / 3) ≤ Real.cos (Real.pi * t) := by
      rw [← Real.cos_abs (Real.pi * t)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      · linarith [Real.pi_pos]
      · exact hpi
    rwa [Real.cos_pi_div_three] at h2
  have hnorm : (1 : ℝ) / 2 ≤ ‖limitAmp a ω‖ := by
    rw [norm_limitAmp, show Real.pi * ((a : ℝ) - 1 / 2) * ω = Real.pi * t by rw [ht]; ring]
    calc (1 : ℝ) / 2 ≤ Real.cos (Real.pi * t) := hcos
      _ ≤ |Real.cos (Real.pi * t)| := le_abs_self _
  have hne : limitAmp a ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  filter_upwards [eventually_norm_F_ge a ω hne] with N hN
  have : (1 / 4 : ℝ) * N ≤ (‖limitAmp a ω‖ / 2) * N := by
    have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  linarith
