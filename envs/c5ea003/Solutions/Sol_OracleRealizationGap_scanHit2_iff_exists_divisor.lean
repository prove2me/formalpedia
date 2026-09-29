-- Prove2me | solution 1 for OracleRealizationGap.scanHit2_iff_exists_divisor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:11:34.565053+00:00
-- url     : https://prove2.me/submissions/810571f3-0cda-4dcd-8aba-8a10d9a94080

-- Sol generated from Novelty/FermatDivisorCorrespondence.lean
import Mathlib
import Definitions.Def_Novelty_FermatDivisorCorrespondence
import Definitions.Def_Novelty_OracleRealizationGap
import Theorems.Thm_OracleRealizationGap_scanHit2_of_split
import Theorems.Thm_OracleRealizationGap_sq_sub_sq

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
theorem solution(N k : ℕ) (hN : 0 < N) :
    ScanHit2 N k ↔ ∃ d, d ∣ N ∧ 1 < d ∧ d < N ∧ d + N / d ≤ Nat.sqrt (4 * N) + k := by
  constructor
  · rintro ⟨i, hik, b, hsq, hnt⟩
    set a := Nat.sqrt (4 * N) + i with ha
    have hba : b < a := by omega
    have hfac : (a - b) * (a + b) = 4 * N := by
      rw [sq_sub_sq a b (le_of_lt hba)]
      exact Nat.sub_eq_of_eq_add hsq
    -- both factors are even, since their sum `2a` is even and their product is even
    have hpar : (a - b) % 2 = (a + b) % 2 := by omega
    have heven : (a - b) % 2 = 0 := by
      by_contra hodd
      have h1 : Odd (a - b) := by rw [Nat.odd_iff]; omega
      have h2 : Odd (a + b) := by rw [Nat.odd_iff]; omega
      have : Odd ((a - b) * (a + b)) := h1.mul h2
      rw [hfac, Nat.odd_iff] at this
      omega
    obtain ⟨d, hd⟩ : ∃ d, a - b = 2 * d := ⟨(a - b) / 2, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, a + b = 2 * e := ⟨(a + b) / 2, by omega⟩
    have hde : d * e = N := by
      have h4 : 4 * (d * e) = 4 * N := by rw [← hfac, hd, he]; ring
      omega
    have hd1 : 1 < d := by omega
    have hdle : d ≤ e := by omega
    have he1 : 1 < e := by omega
    have hdpos : 0 < d := by omega
    have hdiv : N / d = e := by rw [← hde, Nat.mul_div_cancel_left _ hdpos]
    refine ⟨d, ⟨e, hde.symm⟩, hd1, ?_, ?_⟩
    · have : d * 2 ≤ d * e := Nat.mul_le_mul_left _ he1
      omega
    · rw [hdiv]
      omega
  · rintro ⟨d, hdvd, hd1, hdN, hmid⟩
    obtain ⟨e, he⟩ := hdvd
    have hdpos : 0 < d := by omega
    have hdiv : N / d = e := by rw [he, Nat.mul_div_cancel_left _ hdpos]
    rw [hdiv] at hmid
    have he1 : 1 < e := by
      rcases Nat.lt_or_ge e 2 with h | h
      · interval_cases e <;> omega
      · omega
    rcases le_total d e with hde | hed
    · exact scanHit2_of_split he hd1 hde hmid
    · exact scanHit2_of_split (by rw [he]; ring) he1 hed (by omega)
