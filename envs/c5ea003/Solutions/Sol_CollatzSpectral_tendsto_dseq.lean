-- Prove2me | solution 1 for CollatzSpectral.tendsto_dseq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:13:48.702195+00:00
-- url     : https://prove2.me/submissions/49e48c0d-6dcd-4922-9bf8-0f964e7f2e6e

-- Sol generated from Novelty/CollatzSpectralNormalized.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized
import Theorems.Thm_CollatzSpectral_summand_eq

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



@[simp] lemma E_zero : E 0 = 1 := by simp [E]

@[simp] lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  have : (2 : ℂ) * Real.pi * Complex.I * x = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [E, this, Complex.norm_exp_ofReal_mul_I]

lemma continuous_E : Continuous E := by
  unfold E
  fun_prop



/-! ## The maps and their phase ratios -/





/-! ## The cutoff transform -/







/-! ## Convergence of the normalized transform -/


lemma dseq_eq (a : ℕ) (ω : ℝ) (k : ℕ) :
    dseq a ω k = if k % 2 = 0 then E ((a : ℝ) * ω) * (E (ω / (k + 1)) - 1) else 0 := by
  unfold dseq limitAmp branchGap
  rcases Nat.even_or_odd k with hk | hk
  · have hk0 : k % 2 = 0 := Nat.even_iff.mp hk
    rw [summand_eq, if_pos hk0, if_pos hk0, hk.neg_one_pow]
    ring
  · have hk1 : k % 2 = 1 := Nat.odd_iff.mp hk
    rw [summand_eq, if_neg (by omega), if_neg (by omega), hk.neg_one_pow]
    ring

lemma norm_dseq_le (a : ℕ) (ω : ℝ) (k : ℕ) :
    ‖dseq a ω k‖ ≤ ‖E (ω / (k + 1)) - 1‖ := by
  rw [dseq_eq]
  by_cases hk : k % 2 = 0
  · rw [if_pos hk, norm_mul, norm_E, one_mul]
  · rw [if_neg hk, norm_zero]
    positivity




/-! ## The amplitude: modulus, resonances, and the discriminator -/






/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/



open CollatzSpectral in
theorem solution(a : ℕ) (ω : ℝ) : Filter.Tendsto (dseq a ω) Filter.atTop (𝓝 0) := by
  have h0 : Filter.Tendsto (fun k : ℕ => ω / ((k : ℝ) + 1)) Filter.atTop (𝓝 0) := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    have h1 : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right _ 1 this
    simpa using h1.inv_tendsto_atTop.const_mul ω
  have h1 : Filter.Tendsto (fun k : ℕ => E (ω / ((k : ℝ) + 1)) - 1) Filter.atTop (𝓝 0) := by
    have : Filter.Tendsto (fun k : ℕ => E (ω / ((k : ℝ) + 1))) Filter.atTop (𝓝 (E 0)) :=
      (continuous_E.tendsto 0).comp h0
    simpa using this.sub_const 1
  refine squeeze_zero_norm (fun k => ?_) (by simpa using h1.norm)
  simpa using norm_dseq_le a ω k
