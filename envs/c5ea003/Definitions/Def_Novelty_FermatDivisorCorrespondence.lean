-- Prove2me | Definitions.Def_Novelty_FermatDivisorCorrespondence
-- name    : Novelty_FermatDivisorCorrespondence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:26.447914+00:00
-- url     : https://prove2.me/theorems/74cbd41d-d89c-4c13-bf8c-a2235337be4f
-- title:
--   Aether Catalog definitions — Novelty_FermatDivisorCorrespondence
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FermatDivisorCorrespondence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FermatDivisorCorrespondence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap

/-!
# Cycle 2: the navigation sensor for arbitrary odd `N` is a divisor-midpoint minimum

Cycle 1 (`Novelty.OracleRealizationGap`) priced the oracle navigation sensor on *semiprimes*:
a Fermat scan of budget `k` succeeds exactly when the Fermat gap `d = (p+q)/2 - ⌊√N⌋` is at
most `k`.  That statement presupposes the factorisation.  This file removes the hypothesis and
identifies the scan's cost for an arbitrary odd `N` intrinsically:

> a scan of budget `k` succeeds **iff** `N` has a nontrivial divisor `d` whose divisor-pair
> midpoint `(d + N/d)/2` lies within `⌊√N⌋ + k`.

So the navigation sensor of the campaign is, in general, the indicator of

`fermatCost N = min { (d + N/d)/2 - ⌊√N⌋ : d ∣ N, 1 < d < N } ≤ B`,

a minimum over the whole divisor lattice of `N`; on semiprimes the lattice has a single
nontrivial pair and the minimum collapses to the gap of cycle 1.  This is the structural reason
the sensor is factor-conditioned: its value is a *divisor-lattice* functional.

## Main results

* `scanHit_of_split` : an odd factorisation `N = u·v` with `1 < u ≤ v` and midpoint within
  `⌊√N⌋ + k` produces a scan hit;
* `scanHit_iff_exists_divisor` : the intrinsic characterisation, for every odd `N` and budget;
* `not_scanHit_of_all_divisors_far` : the safety criterion — if every divisor-pair midpoint
  overshoots the budget, no scan of that budget succeeds;
* `scanHit_mono`, `exists_scanHit_of_dvd` : monotonicity in the budget and unconditional
  reachability for composite `N`, so the least successful budget (the general navigation gap)
  exists;
* `scanHit_semiprime_iff` : cycle 1's semiprime budget law recovered from the general one.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the sensor threshold statistic is not tied to the *prime*
factorisation at all; it is the distance from `⌊√N⌋` to the nearest divisor-pair midpoint.  If
so, the semiprime law of cycle 1 is one instance of a lattice-wide minimum, and highly composite
`N` should be *easier* to navigate, not harder.

Experiment (Experimenter): `ComputationalEvidence.md`, Table 5: for every odd `N < 20000` the
least budget with a scan hit equals `min over d ∣ N, 1 < d < N of (d + N/d)/2 - ⌊√N⌋` — zero
violations; and for `N` with many divisors the minimum is attained at an interior divisor, not
at the extreme pair.

Analysis (Analyst): the correspondence `d ↔ (a, b) = ((d + N/d)/2, (N/d - d)/2)` is a bijection
between nontrivial divisor pairs and nontrivial Fermat representations.  Everything else — the
budget law, the safety criterion, the semiprime specialisation — is a reading of that bijection.

Critique (Critic): the `1 < d < N` guard is exactly the exclusion of the trivial representation
`N = ((N+1)/2)² - ((N-1)/2)²`; dropping it would make every odd `N` a hit at astronomical
budget and the theorem vacuous.  Oddness of `N` is needed there: for even `N` the divisor pair
may have opposite parities and no integral midpoint exists (`N = 12`, `k = 0`, `d = 3` is a
counterexample to the odd law without the hypothesis).  Cycle 4 repairs this by doubling, where
the guard must be strengthened to `2 < a - b` because `4N = (N+1)² - (N-1)²` has `a - b = 2`.
-/

namespace OracleRealizationGap







/-! ## Cycle 4: removing the parity hypothesis by doubling -/

/-- The doubled scan: probe `⌊√(4N)⌋, …, ⌊√(4N)⌋ + k` for a square remainder, with the
nontriviality guard `2 < a - b` (the doubled split `4N = (N+1)² - (N-1)²` has `a - b = 2`). -/
def ScanHit2 (N k : ℕ) : Prop :=
  ∃ i ≤ k, ∃ b : ℕ, (Nat.sqrt (4 * N) + i) ^ 2 = 4 * N + b ^ 2 ∧ 2 < Nat.sqrt (4 * N) + i - b




end OracleRealizationGap


