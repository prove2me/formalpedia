-- Prove2me | solution 1 for OracleRealizationGap.scanHit_iff_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:14:32.17563+00:00
-- url     : https://prove2.me/submissions/2be429be-df5c-42cb-b613-97fccb7b032d

-- Sol generated from Novelty/OracleRealizationGap.lean
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap
import Theorems.Thm_OracleRealizationGap_exists_half
import Theorems.Thm_OracleRealizationGap_mid_sq
import Theorems.Thm_OracleRealizationGap_sq_sub_sq
import Theorems.Thm_OracleRealizationGap_sqrt_add_gap

/-!
# The oracle-realization gap for the Fermat navigation sensor

Round-74 of the factoring-barriers campaign measured an *oracle navigation sensor* on a
population of odd semiprimes `N = p·q`: the indicator `1{d ≤ B}` of the **Fermat gap**

`d(N) = (p+q)/2 - ⌊√N⌋`

carried `I(1{d ≤ B}; b₁) ≈ 0.48` bits at `B = 22758`, while *no* `N`-computable query policy
with a 295-item menu realised more than a fraction of it (strict within-strata crediting: `0 %`
on both seeds; only a between-strata population base-rate slice survived leniently).  The
experimental verdict was `GAP-PARTIAL`, attributed to *barrier 6 (circularity)*: the sensor is a
function of the hidden factorisation, not of `N`.

This file turns that empirical verdict into theorems.  Three independent mechanisms are proved.

## Main results

* `recover_gap` (**circularity, exactly**): for odd `p ≤ q` the single number `d = gap p q`
  reconstructs the factorisation by two integer square roots:
  `recover (p*q) (gap p q) = p` and `recoverHi (p*q) (gap p q) = q`.
  Knowing the sensor's underlying statistic *is* knowing the factors — the sensor is
  factor-conditioned by construction.
* `scanHit_iff_gap_le` (**budget law**): for a semiprime `N = p·q` with `p, q` odd primes, a
  Fermat scan of budget `k` (probing `⌊√N⌋, …, ⌊√N⌋+k` for a square remainder and demanding a
  nontrivial split) succeeds **iff** `gap p q ≤ k`.  So the geometric channel realises the
  sensor exactly at the price `k ≥ B`, and never below it.
* `least_accepting_eq_gap`, `oracle_factors` (**oracle ⇒ factoring**): any oracle answering the
  thresholded sensor `1{d ≤ B}` for all `B` yields `d`, hence a factorisation.  The `0.48`-bit
  sensor is therefore not merely unrealised but *factoring-hard*.
* `gap_gt_of_far`, `exists_prime_gap_gt` (**menu exhaustion**): the gap is unbounded — for every
  budget `k` there are infinitely many semiprimes whose gap exceeds `k`, so no fixed menu (295
  items, or any finite number) can cover the population.
* `residue_menu_blind`, `residue_policy_errs` (**MODONLY null, structurally**): for *every*
  modulus `L` and every threshold `B` there are two semiprimes with the same residue `mod L`
  and opposite sensor values.  Hence every policy that reads only residues of `N` errs on one of
  them: the residue channel carries exactly zero sensor information, which is the structural
  counterpart of the measured `0.0008–0.0032` bit MODONLY residual.
* `witness_gap`, `witness_scan_295`, `witness_scan_22758` (**the measured window, concretely**):
  `N = 955277 · 1044727 = 998003674379` has `gap = 1001`, so it lies strictly inside the
  reported window `295 < d ≤ 22758`: the sensor fires, and the 295-query scan misses it.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the measured 74–77 % "within-strata geometric excess" is not a
statistical artefact but a theorem: the sensor's statistic is Fermat-equivalent, so realising it
costs exactly the gap in probes, and every bounded-menu policy that is a function of residues is
provably blind.

Experiment (Experimenter): `ComputationalEvidence.md` tabulates `gap p q` for semiprime samples
across five magnitude decades, locates the concrete witness `998003674379` (gap `1001`) inside
the reported `(295, 22758]` window, and checks the budget law `scan k succeeds ↔ gap ≤ k` by
brute force for all odd semiprimes below `10^5`.

Analysis (Analyst): the empirical split "≈ 74 % within-strata geometry + ≈ 24 % population
prior" corresponds to the two theorems `scanHit_iff_gap_le` (geometry, priced in probes) and
`gap_gt_of_far` (unboundedness, which is what the finite menu cannot cover).  The MODONLY null
is not an estimate at all: it is exact, by `residue_policy_errs`.

Critique (Critic): the budget law needs the *nontriviality* guard `1 < a - b`, else the split
`N = ((N+1)/2)² - ((N-1)/2)²` makes every odd `N` a hit at astronomical budget; the guard is
part of `ScanHit`.  Squares `p = q` are legitimate members of the semiprime population and are
used (only) in `residue_menu_blind`, where the *other* member of the colliding pair has two
distinct prime factors; the pair is genuinely mixed.  No theorem here is vacuous: each existence
statement is witnessed, and `witness_gap` is a concrete numeral computation.
-/

open OracleRealizationGap

/-! ## 1.  The Fermat gap and its parametrisation -/









variable {p h : ℕ}

lemma mid_param (p h : ℕ) : mid p (p + 2 * h) = p + h := by
  unfold mid; omega


lemma sqrt_le_param (p h : ℕ) : Nat.sqrt (p * (p + 2 * h)) ≤ p + h := by
  have : p * (p + 2 * h) ≤ (p + h) ^ 2 := by nlinarith
  calc Nat.sqrt (p * (p + 2 * h)) ≤ Nat.sqrt ((p + h) ^ 2) := Nat.sqrt_le_sqrt this
    _ = p + h := Nat.sqrt_eq' _


variable {p q : ℕ}

/-- `⌊√(pq)⌋ ≤ (p+q)/2`: the arithmetic–geometric mean inequality, integer form. -/
lemma sqrt_le_mid (hp : Odd p) (hq : Odd q) (hpq : p ≤ q) :
    Nat.sqrt (p * q) ≤ mid p q := by
  obtain ⟨h, rfl⟩ := exists_half hp hq hpq
  rw [mid_param]; exact sqrt_le_param p h



/-! ## 2.  Barrier 6, exactly: the gap reconstructs the factorisation -/




/-! ## 3.  The budget law for the geometric channel -/


/-! ## 4.  The sensor oracle is factoring-hard -/



/-! ## 5.  Menu exhaustion: the gap is unbounded -/




/-! ## 6.  The residue channel is exactly blind -/



/-! ## 7.  The measured window, concretely -/







open OracleRealizationGap in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpo : Odd p) (hqo : Odd q)
    (hpq : p ≤ q) (k : ℕ) : ScanHit (p * q) k ↔ gap p q ≤ k := by
  constructor
  · rintro ⟨i, hik, b, hsq, hnt⟩
    set s := Nat.sqrt (p * q) with hs
    set a := s + i with ha
    have hba : b < a := by omega
    have hfac : (a - b) * (a + b) = p * q := by
      rw [sq_sub_sq a b (le_of_lt hba)]
      exact Nat.sub_eq_of_eq_add hsq
    have hu2 : 2 ≤ a - b := by omega
    have hle : a - b ≤ a + b := by omega
    -- the split must be `{p, q}`
    have hsum : (a - b) + (a + b) = p + q := by
      have hpd : p ∣ (a - b) * (a + b) := ⟨q, hfac⟩
      rcases (Nat.Prime.dvd_mul hp).1 hpd with hdu | hdv
      · obtain ⟨m, hm⟩ := hdu
        have hmv : m * (a + b) = q := by
          have : p * (m * (a + b)) = p * q := by rw [← hfac, hm]; ring
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        rcases (Nat.Prime.eq_one_or_self_of_dvd hq m ⟨a + b, hmv.symm⟩) with hm1 | hmq
        · subst hm1
          have : a + b = q := by omega
          omega
        · exfalso
          have hv1 : a + b = 1 := by
            subst hmq
            have := hq.pos
            nlinarith [hmv]
          omega
      · obtain ⟨m, hm⟩ := hdv
        have hmu : (a - b) * m = q := by
          have : p * ((a - b) * m) = p * q := by rw [← hfac, hm]; ring
          exact Nat.eq_of_mul_eq_mul_left hp.pos this
        rcases (Nat.Prime.eq_one_or_self_of_dvd hq (a - b) ⟨m, hmu.symm⟩) with hu1 | huq
        · omega
        · have hm1 : m = 1 := by
            have : q * m = q * 1 := by rw [← huq] at hmu ⊢; omega
            exact Nat.eq_of_mul_eq_mul_left hq.pos this
          have hvp : a + b = p := by rw [hm, hm1]; ring
          omega
    have hmideq : a = mid p q := by
      unfold mid; omega
    have hs_le : s ≤ mid p q := sqrt_le_mid hpo hqo hpq
    have : gap p q = i := by unfold gap; omega
    omega
  · intro hgk
    refine ⟨gap p q, hgk, (q - p) / 2, ?_, ?_⟩
    · rw [sqrt_add_gap hpo hqo hpq]
      exact mid_sq hpo hqo hpq
    · rw [sqrt_add_gap hpo hqo hpq]
      have hmid : mid p q = p + (q - p) / 2 := by
        obtain ⟨h, rfl⟩ := exists_half hpo hqo hpq
        rw [mid_param]; omega
      have hp3 : 2 < p := by
        have h1 := Nat.odd_iff.mp hpo
        have h2 := hp.two_le
        omega
      omega
