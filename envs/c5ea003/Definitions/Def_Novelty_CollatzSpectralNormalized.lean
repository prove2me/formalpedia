-- Prove2me | Definitions.Def_Novelty_CollatzSpectralNormalized
-- name    : Novelty_CollatzSpectralNormalized
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:09:57.099554+00:00
-- url     : https://prove2.me/theorems/377ba0e4-05b6-42f5-ad15-a4929941aaf7
-- title:
--   Aether Catalog definitions — Novelty_CollatzSpectralNormalized
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CollatzSpectralNormalized`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CollatzSpectralNormalized.lean by skeleton subtraction
import Mathlib

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

namespace CollatzSpectral

open Filter Complex
open scoped Real Topology

/-! ## The character `e(x) = exp(2π i x)` -/

/-- The additive character `e(x) = exp(2π i x)`. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)







/-! ## The maps and their phase ratios -/

/-- The one-step accelerated `a n + 1` map. -/
def step (a n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else a * n + 1

/-- The phase ratio `step a n / n`. -/
noncomputable def ratio (a n : ℕ) : ℝ := (step a n : ℝ) / (n : ℝ)



/-! ## The cutoff transform -/

/-- The cutoff exponential sum `F a ω N = ∑_{n=1}^{N} e(ω · ratio a n)`. -/
noncomputable def F (a : ℕ) (ω : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, E (ω * ratio a (k + 1))

/-- The limiting normalized amplitude `(e(ω/2) + e(aω))/2`. -/
noncomputable def limitAmp (a : ℕ) (ω : ℝ) : ℂ := (E (ω / 2) + E (a * ω)) / 2

/-- Half the difference of the two branch phases. -/
noncomputable def branchGap (a : ℕ) (ω : ℝ) : ℂ := (E (a * ω) - E (ω / 2)) / 2




/-! ## Convergence of the normalized transform -/

/-- The deviation of the `k`-th summand from its two-periodic model. -/
noncomputable def dseq (a : ℕ) (ω : ℝ) (k : ℕ) : ℂ :=
  E (ω * ratio a (k + 1)) - (limitAmp a ω + (-1) ^ k * branchGap a ω)






/-! ## The amplitude: modulus, resonances, and the discriminator -/






/-! ## An arithmetic discriminator between the `3n+1`, `5n+1` and `7n+1` maps -/





/-! ## The averaged (L²) statistic does not discriminate -/


end CollatzSpectral


