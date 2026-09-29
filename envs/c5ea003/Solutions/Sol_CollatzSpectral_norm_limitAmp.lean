-- Prove2me | solution 1 for CollatzSpectral.norm_limitAmp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:10:18.7179+00:00
-- url     : https://prove2.me/submissions/d7611e5c-d596-4674-8ac7-ce5e2268bfbd

-- Sol generated from Novelty/CollatzSpectralNormalized.lean
import Mathlib
import Definitions.Def_Novelty_CollatzSpectralNormalized

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


lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  push_cast
  ring_nf

@[simp] lemma E_zero : E 0 = 1 := by simp [E]

@[simp] lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  have : (2 : ℂ) * Real.pi * Complex.I * x = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [E, this, Complex.norm_exp_ofReal_mul_I]


/-- `e(x) + e(-x) = 2 cos(2π x)`. -/
lemma E_add_E_neg (x : ℝ) : E x + E (-x) = 2 * (Real.cos (2 * Real.pi * x) : ℂ) := by
  rw [E, E, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

/-- `‖1 + e(t)‖ = 2 |cos(π t)|`. -/
lemma norm_one_add_E (t : ℝ) : ‖1 + E t‖ = 2 * |Real.cos (Real.pi * t)| := by
  have ha : t / 2 + -(t / 2) = 0 := by ring
  have hb : t / 2 + t / 2 = t := by ring
  have h1 : 1 + E t = E (t / 2) * (E (-(t / 2)) + E (t / 2)) := by
    rw [mul_add, ← E_add, ← E_add, ha, hb, E_zero]
  have harg : 2 * Real.pi * (t / 2) = Real.pi * t := by ring
  have h2 : E (-(t / 2)) + E (t / 2) = 2 * ((Real.cos (Real.pi * t) : ℝ) : ℂ) := by
    rw [add_comm, E_add_E_neg (t / 2), harg]
  rw [h1, h2, norm_mul, norm_E, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-! ## The maps and their phase ratios -/





/-! ## The cutoff transform -/







/-! ## Convergence of the normalized transform -/







/-! ## The amplitude: modulus, resonances, and the discriminator -/






/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/



open CollatzSpectral in
theorem solution(a : ℕ) (ω : ℝ) :
    ‖limitAmp a ω‖ = |Real.cos (Real.pi * ((a : ℝ) - 1 / 2) * ω)| := by
  have harg : ω / 2 + ((a : ℝ) - 1 / 2) * ω = (a : ℝ) * ω := by ring
  have hsplit : E (ω / 2) + E ((a : ℝ) * ω)
      = E (ω / 2) * (1 + E (((a : ℝ) - 1 / 2) * ω)) := by
    rw [mul_add, mul_one, ← E_add, harg]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  unfold limitAmp
  rw [hsplit, norm_div, norm_mul, norm_E, one_mul, norm_one_add_E, h2,
    show Real.pi * (((a : ℝ) - 1 / 2) * ω) = Real.pi * ((a : ℝ) - 1 / 2) * ω by ring]
  ring
