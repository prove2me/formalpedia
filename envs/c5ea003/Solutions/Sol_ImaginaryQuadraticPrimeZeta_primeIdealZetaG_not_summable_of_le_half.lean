-- Prove2me | solution 1 for ImaginaryQuadraticPrimeZeta.primeIdealZetaG_not_summable_of_le_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:08:29.519214+00:00
-- url     : https://prove2.me/submissions/bd549f19-f5a2-46ad-a4b0-04e22df4ffb3

-- Sol generated from Novelty/ImaginaryQuadraticPrimeZetaGeneral.lean
import Mathlib
import Definitions.Def_Novelty_ImaginaryQuadraticPrimeZeta
import Definitions.Def_Novelty_ImaginaryQuadraticPrimeZetaGeneral
import Definitions.Def_Novelty_PrimeZetaAbscissa

/-!
# Abscissa bracket for a general imaginary quadratic prime-ideal zeta function

This file abstracts the Gaussian computation of
`Catalog.Novelty.ImaginaryQuadraticPrimeZeta` to an **arbitrary** imaginary
quadratic field `K` with class number one.  The arithmetic of such a field is
encoded by its *splitting data* at each rational prime `p`:

* `deg1` is the number of degree-one prime ideals above `p` (each of norm `p`);
  it satisfies `deg1 p ≤ 2`.
* `inert` is the number of degree-two (inert) prime ideals above `p` (each of
  norm `p²`); it satisfies `inert p ≤ 1`.

Since every rational prime has at least one prime ideal above it, the splitting
data always satisfies `1 ≤ deg1 p + inert p`.  The associated prime-ideal zeta
function is `P_K(s) = ∑_p (deg1 p)·p^{-s} + (inert p)·p^{-2s}`.

## Main results

* `primeIdealZetaG_summable` — convergence for `s > 1` (degree-two structure).
* `primeIdealZetaG_not_summable_of_le_half` — divergence for `s ≤ 1/2`, forced by
  the unavoidable prime ideals of norm `≤ p²`.
* `primeIdealZetaG_not_summable_nonpos` — divergence on the whole half-line
  `s ≤ 0`; in particular at `s = -1`, the formal "sum/product of all prime
  ideals" point, the bare series has no value: **no regularization can come from
  the series itself**.
* `gaussTerm_eq_primeIdealZetaGTerm` and `gaussPrimeZeta_eq_primeIdealZetaG` —
  the Gaussian field `ℚ(i)` of the companion file is the instance of this general
  framework with the explicit `p mod 4` splitting data.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "The abscissa bracket `[1/2, 1]` and the `s ≤ 0`
regularization obstruction are *structural*: they depend only on `deg1 ≤ 2`,
`inert ≤ 1`, and `deg1 + inert ≥ 1`, not on the specific field."
Experiment (Experimenter): Replaced the `ℚ(i)`-specific `gaussTerm` by the
two-parameter family `primeIdealZetaGTerm deg1 inert` and re-derived the same
pointwise sandwich `p^{-2s} ≤ term ≤ 2·p^{-s} + p^{-2s}`; the previous file is
recovered by `gaussTerm_eq_primeIdealZetaGTerm`.
Analysis (Analyst): The convergence floor `1/2` is set by the *inert* norm-`p²`
ideals; the regularization obstruction at `s ≤ 0` is set by the fact that for
`s ≤ 0` every term is `≥ 1`, so the series cannot even tend to `0`.  Both are
field-independent.
Critique (Critic): Checked that the `s ≤ 0` divergence does not secretly assume
convergence anywhere, that the lower bound uses the honest hypothesis
`1 ≤ deg1 p + inert p`, and that the bridge lemmas are definitional matches (no
hidden re-proof of the catalog results).
Synthesis (PI): The only field-dependent ingredient left is the *sharp* abscissa
`1`, which needs positive density of split primes — exactly the Dirichlet-density
input flagged for the natural-boundary conjecture in `FUTURE_DIRECTIONS.md`.
-/

open scoped BigOperators

open ImaginaryQuadraticPrimeZeta



/-
Each term of the general prime-ideal zeta series is nonnegative.
-/

/-
**Convergence (upper abscissa `≤ 1`).** For splitting data bounded by the
degree (`deg1 ≤ 2`, `inert ≤ 1`) the general prime-ideal zeta series converges
absolutely for every `s > 1`.
-/

/-
**Divergence (lower abscissa `≥ 1/2`).** Whenever every rational prime has at
least one prime ideal above it (`1 ≤ deg1 p + inert p`), the series diverges for
all `s ≤ 1/2`.
-/

/-
**Regularization obstruction.** For `s ≤ 0` (in particular at `s = -1`, the
formal "sum of all prime ideals" point) every term is `≥ 1`, so the bare series
diverges: no value at `s = -1` can come from the series itself.
-/



/-
**Bridge to `ℚ(i)`.** The Gaussian term of the companion file is exactly the
general term for the Gaussian splitting data.
-/

/-
**Bridge to `ℚ(i)`.** The Gaussian prime-ideal zeta function is the instance
of the general framework with the explicit `p mod 4` splitting data.
-/

/-
The Gaussian splitting data satisfies the structural hypotheses: every prime
has at least one prime ideal above it.
-/


open ImaginaryQuadraticPrimeZeta in
theorem solution{deg1 inert : Nat.Primes → ℕ}
    (hpos : ∀ p, 1 ≤ deg1 p + inert p) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    ¬ Summable (fun p : Nat.Primes => primeIdealZetaGTerm deg1 inert s p) := by
  -- Since `s ≤ 1/2`, we have `-(2*s) ≥ -1`.
  have h_exp : ∀ p : Nat.Primes, (p : ℝ) ^ (-(2 * s)) ≤ primeIdealZetaGTerm deg1 inert s p := by
    intro p
    have h_pow : (p : ℝ) ^ (-(2 * s)) ≤ (deg1 p : ℝ) * (p : ℝ) ^ (-s) + (inert p : ℝ) * (p : ℝ) ^ (-(2 * s)) := by
      have h_lower_bound : (deg1 p : ℝ) * (p : ℝ) ^ (-s) + (inert p : ℝ) * (p : ℝ) ^ (-(2 * s)) ≥ (deg1 p + inert p : ℝ) * (p : ℝ) ^ (-(2 * s)) := by
        rw [ add_mul ];
        exact add_le_add ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( mod_cast p.2.one_lt.le ) ( by linarith ) ) ( Nat.cast_nonneg _ ) ) le_rfl;
      exact le_trans ( le_mul_of_one_le_left ( by positivity ) ( mod_cast hpos p ) ) h_lower_bound
    exact h_pow;
  -- By comparison, if the term series were summable, the smaller nonneg series `(p)^(-(2*s))` would be summable too.
  by_contra h_contra
  have h_summable : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * s))) := by
    exact Summable.of_nonneg_of_le ( fun p => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) h_exp h_contra;
  have := @Nat.Primes.summable_rpow;
  exact absurd ( this.mp h_summable ) ( by linarith )
