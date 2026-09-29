-- Prove2me | solution 1 for CollatzSpectral.tendsto_F_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:16:03.363844+00:00
-- url     : https://prove2.me/submissions/81a16bc5-8d21-405e-83a1-7a2696af51d5

-- Sol generated from Novelty/CollatzSpectralNormalized.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized
import Theorems.Thm_CollatzSpectral_tendsto_dseq

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





/-- Exact decomposition of the partial sum into the mean term, the alternating
term, and the deviation sum. -/
lemma F_eq (a : ℕ) (ω : ℝ) (N : ℕ) :
    F a ω N = (N : ℂ) * limitAmp a ω
      + branchGap a ω * (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k)
      + ∑ k ∈ Finset.range N, dseq a ω k := by
  unfold F dseq
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring


/-! ## The amplitude: modulus, resonances, and the discriminator -/






/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/



open CollatzSpectral in
theorem solution(a : ℕ) (ω : ℝ) :
    Filter.Tendsto (fun N : ℕ => F a ω N / (N : ℂ)) Filter.atTop (𝓝 (limitAmp a ω)) := by
  have hces : Filter.Tendsto (fun N : ℕ => ((N : ℝ))⁻¹ • ∑ k ∈ Finset.range N, dseq a ω k)
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_dseq a ω).cesaro_smul
  have hces' : Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, dseq a ω k)
      Filter.atTop (𝓝 0) := by
    refine hces.congr (fun N => ?_)
    rw [Complex.real_smul]
    push_cast
    ring
  have hbnd : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * (branchGap a ω * ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k)‖
      ≤ ‖branchGap a ω‖ / N := by
    intro N
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
    have hb : ‖∑ k ∈ Finset.range N, (-1 : ℂ) ^ k‖ ≤ 1 := by
      rw [neg_one_geom_sum]
      by_cases h : Even N <;> simp [h]
    have h1 : ‖branchGap a ω‖ * ‖∑ k ∈ Finset.range N, (-1 : ℂ) ^ k‖
        ≤ ‖branchGap a ω‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    calc (N : ℝ)⁻¹ * (‖branchGap a ω‖ * ‖∑ k ∈ Finset.range N, (-1 : ℂ) ^ k‖)
        ≤ (N : ℝ)⁻¹ * (‖branchGap a ω‖ * 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖branchGap a ω‖ / N := by rw [mul_one]; ring
  have halt : Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      (branchGap a ω * ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k)) Filter.atTop (𝓝 0) :=
    squeeze_zero_norm hbnd (tendsto_const_div_atTop_nhds_zero_nat ‖branchGap a ω‖)
  have hmain : Filter.Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      (branchGap a ω * ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k)
      + (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, dseq a ω k + limitAmp a ω)
      Filter.atTop (𝓝 (limitAmp a ω)) := by
    simpa using ((halt.add hces').add_const (limitAmp a ω))
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [F_eq]
  field_simp
  ring
