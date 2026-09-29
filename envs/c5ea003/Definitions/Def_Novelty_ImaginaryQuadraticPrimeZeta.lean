-- Prove2me | Definitions.Def_Novelty_ImaginaryQuadraticPrimeZeta
-- name    : Novelty_ImaginaryQuadraticPrimeZeta
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:13.61789+00:00
-- url     : https://prove2.me/theorems/4b6f1d82-5503-4706-a539-9b9535009fe7
-- title:
--   Aether Catalog definitions — Novelty_ImaginaryQuadraticPrimeZeta
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ImaginaryQuadraticPrimeZeta`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ImaginaryQuadraticPrimeZeta.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_PrimeZetaAbscissa

/-!
# The prime-ideal zeta function of an imaginary quadratic field (the Gaussian case)

This file develops the elementary, fully rigorous core behind the
(physically/number-theoretically motivated) **prime zeta function of an
imaginary quadratic field with class number one**, taking the Gaussian field
`K = ℚ(i)` (discriminant `-4`, class number `1`) as the running model.

For a number field `K` the *prime-ideal zeta function* is
`P_K(s) = ∑_{𝔭 prime ideal} N(𝔭)^{-s}`.  For `K = ℚ(i)` the splitting of a
rational prime `p` in the Gaussian integers `ℤ[i]` is governed by `p mod 4`:

* `p = 2` is **ramified**: one prime ideal of norm `2`              (term `2^{-s}`);
* `p ≡ 1 (mod 4)` is **split**: two prime ideals of norm `p`       (term `2·p^{-s}`);
* `p ≡ 3 (mod 4)` is **inert**: one prime ideal of norm `p²`       (term `p^{-2s}`).

We package this as the single Dirichlet series `gaussPrimeZeta`.

## Main results

* `gaussPrimeZeta_summable` — convergence for every `s > 1` (upper abscissa `≤ 1`),
  using the genuine degree-two structure (the factor `2` on split primes and the
  `p^{-2s}` inert terms).
* `gaussPrimeZeta_not_summable_of_le_half` — divergence for every `s ≤ 1/2`
  (lower abscissa `≥ 1/2`), forced by the *inert* primes of norm `p²`.
* `gaussPrimeZeta_pos` — strict positivity in the region of convergence.
* `gaussPrimeZeta_le_two_primeZeta` — a quantitative bridge to the rational
  prime zeta function `primeZeta` of `Catalog.Novelty.PrimeZetaAbscissa`:
  `P_{ℚ(i)}(s) ≤ 2·P(s)` for `s > 1`.

The sharp statement that the abscissa is *exactly* `1` (and the conjectural
natural boundary along the imaginary axis) is discussed in `FUTURE_DIRECTIONS.md`;
it requires positive Dirichlet density of the split primes `p ≡ 1 (mod 4)`,
which is genuinely deeper than the elementary comparison estimates proved here.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "The prime-ideal zeta of an imaginary quadratic field
should have the same abscissa `1` as the rational prime zeta, but the *floor* of
its convergence is set by the inert primes (norm `p²`), which alone already force
divergence up to `s = 1/2`."
Experiment (Experimenter): Modelled `ℚ(i)` faithfully by the `p mod 4` splitting
and reduced every estimate to two pointwise bounds: `p^{-2s} ≤ term ≤ 2·p^{-s}`
(for `s ≥ 0`), then fed them to `Summable.of_nonneg_of_le` against the rational
prime zeta series from the catalog file.
Analysis (Analyst): The upper bound `term ≤ 2 p^{-s}` gives convergence for
`s > 1` unconditionally; the lower bound `term ≥ p^{-2s}` gives divergence for
`s ≤ 1/2` unconditionally.  The remaining window `(1/2, 1]` is exactly where the
*split* primes must be shown to have positive density — true (Dirichlet) but not
elementary, hence left as a conjecture.
Critique (Critic): Verified the series is not vacuous (the prime `2` gives a
strictly positive term), that the divergence uses an honest inert lower bound and
not a degenerate empty sum, and that the bridge genuinely consumes the catalog
lemma `primeZeta_summable_iff`.
Synthesis (PI): The two-sided abscissa bracket `[1/2, 1]` cleanly isolates the
inert contribution (the unconditional floor) from the split contribution (the
conjectural ceiling and natural-boundary phenomenon).
-/

open scoped BigOperators

namespace ImaginaryQuadraticPrimeZeta

/-- The per-prime term of the Gaussian prime-ideal zeta function, encoding the
`p mod 4` splitting law in `ℤ[i]`. -/
noncomputable def gaussTerm (s : ℝ) (p : Nat.Primes) : ℝ :=
  if (p : ℕ) = 2 then (2 : ℝ) ^ (-s)
  else if (p : ℕ) % 4 = 1 then 2 * (p : ℝ) ^ (-s)
  else (p : ℝ) ^ (-(2 * s))

/-- The **Gaussian prime-ideal zeta function**
`P_{ℚ(i)}(s) = ∑_{𝔭} N(𝔭)^{-s}`, organised over the rational primes below `𝔭`. -/
noncomputable def gaussPrimeZeta (s : ℝ) : ℝ := ∑' p : Nat.Primes, gaussTerm s p

/-
Every term of the Gaussian prime-ideal zeta series is nonnegative.
-/

/-
Pointwise upper bound: each term is at most `2 · p^{-s}` (for `s ≥ 0`).
-/

/-
Pointwise lower bound: each term is at least `p^{-2s}` (for `s ≥ 0`),
the contribution of an inert prime of norm `p²`.
-/

/-
**Convergence (upper abscissa `≤ 1`).** The Gaussian prime-ideal zeta series
converges absolutely for every `s > 1`.
-/

/-
**Divergence (lower abscissa `≥ 1/2`).** For `s ≤ 1/2` the Gaussian
prime-ideal zeta series diverges: the inert primes of norm `p²` already prevent
convergence.
-/

/-
In its region of convergence the Gaussian prime-ideal zeta function is
strictly positive (the ramified prime `2` contributes a positive term).
-/

/-
**Bridge to the rational prime zeta function.** For `s > 1` the Gaussian
prime-ideal zeta is dominated by twice the rational prime zeta function
`primeZeta` of `Catalog.Novelty.PrimeZetaAbscissa`.
-/

end ImaginaryQuadraticPrimeZeta


