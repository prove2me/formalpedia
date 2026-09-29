-- Prove2me | solution 1 for CollatzSpectral.F_even_odd_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:10:17.237707+00:00
-- url     : https://prove2.me/submissions/af2a4b36-38bc-498a-b4ec-9aa8ed3d9df2

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








/-! ## The maps and their phase ratios -/





/-! ## The cutoff transform -/





lemma card_odd_range (n : ℕ) : ((Finset.range n).filter (fun k => k % 2 = 1)).card = n / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : m % 2 = 1
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [if_neg h, ih]; omega


/-! ## Convergence of the normalized transform -/







/-! ## The amplitude: modulus, resonances, and the discriminator -/






/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/



open CollatzSpectral in
theorem solution(a : ℕ) (ω : ℝ) (N : ℕ) :
    F a ω N = (N / 2 : ℕ) * E (ω / 2)
      + E ((a : ℝ) * ω) * ∑ k ∈ (Finset.range N).filter (fun k => k % 2 = 0),
          E (ω / (k + 1)) := by
  classical
  unfold F
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun k => k % 2 = 0)]
  have h1 : ∑ k ∈ (Finset.range N).filter (fun k => k % 2 = 0), E (ω * ratio a (k + 1))
      = E ((a : ℝ) * ω) * ∑ k ∈ (Finset.range N).filter (fun k => k % 2 = 0), E (ω / (k + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk0 : k % 2 = 0 := (Finset.mem_filter.mp hk).2
    rw [summand_eq, if_pos hk0]
  have h2 : ∑ k ∈ (Finset.range N).filter (fun k => ¬ k % 2 = 0), E (ω * ratio a (k + 1))
      = ((Finset.range N).filter (fun k => ¬ k % 2 = 0)).card • E (ω / 2) := by
    rw [← Finset.sum_const]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk0 : ¬ k % 2 = 0 := (Finset.mem_filter.mp hk).2
    rw [summand_eq, if_neg hk0]
  have hfil : (Finset.range N).filter (fun k => ¬ k % 2 = 0)
      = (Finset.range N).filter (fun k => k % 2 = 1) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · intro h; omega
    · intro h; omega
  have hcard : ((Finset.range N).filter (fun k => ¬ k % 2 = 0)).card = N / 2 := by
    rw [hfil, card_odd_range]
  rw [h1, h2, hcard, nsmul_eq_mul]
  ring
