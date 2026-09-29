-- Prove2me | solution 1 for CollatzSpectral.meanSquare_limitAmp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:13:46.890737+00:00
-- url     : https://prove2.me/submissions/0c9f7840-dd75-4acb-ab90-92afa47a62f4

-- Sol generated from Novelty/CollatzSpectralNormalized.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized
import Theorems.Thm_CollatzSpectral_norm_limitAmp

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






/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/



open CollatzSpectral in
theorem solution(a : ℕ) (ha : 1 ≤ a) :
    (∫ ω in (0 : ℝ)..2, ‖limitAmp a ω‖ ^ 2) = 1 := by
  have hkey : ∀ ω : ℝ, ‖limitAmp a ω‖ ^ 2
      = 1 / 2 + Real.cos (Real.pi * (2 * (a : ℝ) - 1) * ω) / 2 := by
    intro ω
    rw [norm_limitAmp, sq_abs]
    rw [Real.cos_sq (Real.pi * ((a : ℝ) - 1 / 2) * ω),
      show 2 * (Real.pi * ((a : ℝ) - 1 / 2) * ω) = Real.pi * (2 * (a : ℝ) - 1) * ω by ring]
  have hc : (2 * (a : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  rw [intervalIntegral.integral_congr (g := fun ω => 1 / 2 + Real.cos (Real.pi * (2 * (a : ℝ) - 1) * ω) / 2)
      (fun ω _ => hkey ω)]
  have hint : (∫ ω in (0 : ℝ)..2, Real.cos (Real.pi * (2 * (a : ℝ) - 1) * ω)) = 0 := by
    have hcc : (Real.pi * (2 * (a : ℝ) - 1)) ≠ 0 := mul_ne_zero (ne_of_gt Real.pi_pos) hc
    have hs : Real.sin (Real.pi * (2 * (a : ℝ) - 1) * 2) = 0 := by
      have hrw : Real.pi * (2 * (a : ℝ) - 1) * 2 = ((2 * (a : ℤ) - 1) * 2 : ℤ) * Real.pi := by
        push_cast; ring
      rw [hrw, Real.sin_int_mul_pi]
    rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) hcc, integral_cos]
    simp [hs]
  have hcosint : (∫ ω in (0 : ℝ)..2, Real.cos (Real.pi * (2 * (a : ℝ) - 1) * ω) / 2) = 0 := by
    rw [intervalIntegral.integral_div, hint]
    simp
  have hcont : Continuous fun x : ℝ => Real.cos (Real.pi * (2 * (a : ℝ) - 1) * x) / 2 := by
    fun_prop
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), hcosint]
  simp
