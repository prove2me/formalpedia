-- Prove2me | solution 1 for OracleRealizationGap.scanHit_iff_exists_divisor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:14:31.593406+00:00
-- url     : https://prove2.me/submissions/cbb148b6-d8c8-44d6-815e-506816d2d52d

-- Sol generated from Novelty/FermatDivisorCorrespondence.lean
import Mathlib
import Definitions.Def_Novelty_FermatDivisorCorrespondence
import Definitions.Def_Novelty_OracleRealizationGap
import Theorems.Thm_OracleRealizationGap_scanHit_of_split
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

/-- A divisor of an odd number is odd. -/
lemma odd_of_dvd_odd {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by
  by_contra hcon
  rw [Nat.not_odd_iff_even] at hcon
  have h2 : (2 : ℕ) ∣ N := dvd_trans hcon.two_dvd hd
  rw [Nat.odd_iff] at hN
  omega






/-! ## Cycle 4: removing the parity hypothesis by doubling -/






open OracleRealizationGap in
theorem solution(N k : ℕ) (hN : Odd N) :
    ScanHit N k ↔ ∃ d, d ∣ N ∧ 1 < d ∧ d < N ∧ (d + N / d) / 2 ≤ Nat.sqrt N + k := by
  constructor
  · rintro ⟨i, hik, b, hsq, hnt⟩
    set a := Nat.sqrt N + i with ha
    have hba : b < a := by omega
    have hfac : (a - b) * (a + b) = N := by
      rw [sq_sub_sq a b (le_of_lt hba)]
      exact Nat.sub_eq_of_eq_add hsq
    have hdvd : (a - b) ∣ N := ⟨a + b, hfac.symm⟩
    have hpos : 0 < a - b := by omega
    have hdiv : N / (a - b) = a + b := by
      rw [← hfac, Nat.mul_div_cancel_left _ hpos]
    refine ⟨a - b, hdvd, by omega, ?_, ?_⟩
    · -- `a - b ≤ a + b` and both exceed `1`, so `a - b` is a proper divisor
      have h2 : 2 ≤ a - b := by omega
      have hab : 2 ≤ a + b := by omega
      have hkey : (a - b) * 2 ≤ (a - b) * (a + b) := Nat.mul_le_mul_left _ hab
      rw [hfac] at hkey
      omega
    · rw [hdiv]
      have : (a - b + (a + b)) / 2 = a := by omega
      omega
  · rintro ⟨d, hdvd, hd1, hdN, hmid⟩
    obtain ⟨e, he⟩ := hdvd
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exact absurd (h ▸ hN) (by simp)
      · exact h
    have hdpos : 0 < d := by omega
    have hdiv : N / d = e := by rw [he, Nat.mul_div_cancel_left _ hdpos]
    rw [hdiv] at hmid
    have hdo : Odd d := odd_of_dvd_odd hN ⟨e, he⟩
    have heo : Odd e := odd_of_dvd_odd hN ⟨d, by rw [he]; ring⟩
    have he1 : 1 < e := by
      rcases Nat.lt_or_ge e 2 with h | h
      · interval_cases e <;> omega
      · omega
    rcases le_total d e with hde | hed
    · exact scanHit_of_split hdo heo hde he hd1 hmid
    · refine scanHit_of_split heo hdo hed (by rw [he]; ring) he1 ?_
      have : e + d = d + e := by ring
      omega
