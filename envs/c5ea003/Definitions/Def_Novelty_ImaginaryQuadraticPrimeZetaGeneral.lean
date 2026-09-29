-- Prove2me | Definitions.Def_Novelty_ImaginaryQuadraticPrimeZetaGeneral
-- name    : Novelty_ImaginaryQuadraticPrimeZetaGeneral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:44.714573+00:00
-- url     : https://prove2.me/theorems/4985ce2b-d5ab-473b-94dc-85b4dd091dd1
-- title:
--   Aether Catalog definitions — Novelty_ImaginaryQuadraticPrimeZetaGeneral
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ImaginaryQuadraticPrimeZetaGeneral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ImaginaryQuadraticPrimeZetaGeneral.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ImaginaryQuadraticPrimeZeta
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

namespace ImaginaryQuadraticPrimeZeta

/-- The per-prime term of the prime-ideal zeta function of an imaginary quadratic
field with splitting data `(deg1, inert)`: `deg1 p` ideals of norm `p` and
`inert p` ideals of norm `p²`. -/
noncomputable def primeIdealZetaGTerm (deg1 inert : Nat.Primes → ℕ) (s : ℝ)
    (p : Nat.Primes) : ℝ :=
  (deg1 p : ℝ) * (p : ℝ) ^ (-s) + (inert p : ℝ) * (p : ℝ) ^ (-(2 * s))

/-- The general imaginary quadratic prime-ideal zeta function. -/
noncomputable def primeIdealZetaG (deg1 inert : Nat.Primes → ℕ) (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, primeIdealZetaGTerm deg1 inert s p

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

/-- The Gaussian splitting data: number of degree-one prime ideals of `ℤ[i]`. -/
def gaussDeg1 (p : Nat.Primes) : ℕ :=
  if (p : ℕ) = 2 then 1 else if (p : ℕ) % 4 = 1 then 2 else 0

/-- The Gaussian splitting data: number of inert (norm `p²`) prime ideals. -/
def gaussInert (p : Nat.Primes) : ℕ :=
  if (p : ℕ) = 2 then 0 else if (p : ℕ) % 4 = 1 then 0 else 1

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

end ImaginaryQuadraticPrimeZeta


