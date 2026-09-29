-- Prove2me | Definitions.Def_Novelty_FermatCloseDensity
-- name    : Novelty_FermatCloseDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:28.073085+00:00
-- url     : https://prove2.me/theorems/a3e16eff-4daa-4ba1-a8bb-1039167d0db9
-- title:
--   Aether Catalog definitions — Novelty_FermatCloseDensity
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FermatCloseDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FermatCloseDensity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap

/-!
# Sparsity of the Fermat-close population: the hit rate is a population artefact

The round-74 measurement reports a sensor hit rate of `0.2053` at threshold `B = 22758` on a
laboratory population of semiprimes, and flags as an honest limit that this rate reflects the
population's size-ratio coupling rather than a property of semiprimes at large.

This file proves that limit.  For a *fixed* threshold `B`, the integers `N ≤ X` admitting a
Fermat-close factorisation (`N = pq` with `p, q` odd, `p ≤ q` and `gap p q ≤ B`) number at most

`(⌊√X⌋ + B + 1) · (⌊√(2B(⌊√X⌋+B))⌋ + 1)`,

which is of order `√B · X^{3/4}` — density `O(√B · X^{-1/4}) → 0`.  A fixed hit rate of `0.2053`
is therefore impossible in the limit: it is a feature of the finite lab population.

## Main results

* `closeSet_subset_image` : every Fermat-close `N ≤ X` is a difference of squares `a² - h²` with
  `a ≤ ⌊√X⌋ + B` and `h ≤ ⌊√(2B(⌊√X⌋+B))⌋`;
* `closeSet_ncard_le` : hence the explicit counting bound above;
* `closeSet_ncard_le_three_quarter` : the same bound in `X^{1/2} · X^{1/4}` shape, via
  submultiplicativity of `Nat.sqrt`;
* `sqrt_mul_le` : `⌊√(uv)⌋ ≤ (⌊√u⌋+1)(⌊√v⌋+1)`, the auxiliary submultiplicativity.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the observed hit rate cannot persist: Fermat-close integers are
governed by two free parameters `(a, h)` with `h` of size at most `√(2Ba)`, so they occupy a
`X^{3/4}`-sized slice of `[1, X]` — a vanishing density.

Experiment (Experimenter): `ComputationalEvidence.md` counts Fermat-close semiprimes below
`10^4, 10^5, 10^6` for `B ∈ {1, 4, 16}` and records the shrinking empirical density.

Analysis (Analyst): the counting is entirely structural — the parametrisation `N = a² - h²` is
injective, and the gap constraint bounds `h` by `√(2Ba)`.  No sieve or analytic input is needed,
which is why the bound is unconditional and explicit.

Critique (Critic): the bound counts *all* differences of squares with odd factors, hence a
superset of semiprimes — that only strengthens it.  It is stated with `Set.ncard`, which is
`0` for infinite sets, so the enclosing finite superset is exhibited explicitly to make the
statement non-vacuous.
-/

namespace OracleRealizationGap

open Finset

/-- The Fermat-close population up to `X` at threshold `B`. -/
def closeSet (X B : ℕ) : Set ℕ :=
  {N | N ≤ X ∧ ∃ p q : ℕ, Odd p ∧ Odd q ∧ p ≤ q ∧ N = p * q ∧ gap p q ≤ B}

/-- The enclosing box of Fermat parameters `(a, h)`. -/
def closeBox (X B : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (Nat.sqrt X + B + 1) ×ˢ Finset.range (Nat.sqrt (2 * B * (Nat.sqrt X + B)) + 1)





end OracleRealizationGap


