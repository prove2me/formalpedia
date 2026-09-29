-- Prove2me | solution 1 for OracleRealizationGap.scanHit_of_split
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:12:53.62304+00:00
-- url     : https://prove2.me/submissions/9021b442-5757-4886-816b-f65b98d3ce8b

-- Sol generated from Novelty/FermatDivisorCorrespondence.lean
import Mathlib
import Definitions.Def_Novelty_FermatDivisorCorrespondence
import Definitions.Def_Novelty_OracleRealizationGap
import Theorems.Thm_OracleRealizationGap_exists_half
import Theorems.Thm_OracleRealizationGap_sq_param

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

open OracleRealizationGap







/-! ## Cycle 4: removing the parity hypothesis by doubling -/






open OracleRealizationGap in
theorem solution{N k u v : ℕ} (hu : Odd u) (hv : Odd v) (huv : u ≤ v)
    (hN : N = u * v) (h1 : 1 < u) (hmid : (u + v) / 2 ≤ Nat.sqrt N + k) : ScanHit N k := by
  obtain ⟨h, rfl⟩ := exists_half hu hv huv
  have hNe : N = u * (u + 2 * h) := hN
  have hsq : (u + h) ^ 2 = N + h ^ 2 := by rw [hNe]; exact sq_param u h
  have hmid' : u + h ≤ Nat.sqrt N + k := by
    have : (u + (u + 2 * h)) / 2 = u + h := by omega
    omega
  have hge : Nat.sqrt N ≤ u + h := by
    have hle : N ≤ (u + h) ^ 2 := by omega
    calc Nat.sqrt N ≤ Nat.sqrt ((u + h) ^ 2) := Nat.sqrt_le_sqrt hle
      _ = u + h := Nat.sqrt_eq' _
  refine ⟨u + h - Nat.sqrt N, by omega, h, ?_, ?_⟩
  · have : Nat.sqrt N + (u + h - Nat.sqrt N) = u + h := by omega
    rw [this, hsq]
  · have : Nat.sqrt N + (u + h - Nat.sqrt N) = u + h := by omega
    omega
