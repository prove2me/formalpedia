-- Prove2me | Theorems.Thm_OracleRealizationGap_mid_sq
-- name    : OracleRealizationGap.mid_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:18:40.922838+00:00
-- url     : https://prove2.me/theorems/5cdfeb3d-0cad-4a84-a09f-35f5da7f79da
-- title:
--   The midpoint squared exceeds `N` by exactly the squared half-difference.
-- statement:
--   The midpoint squared exceeds `N` by exactly the squared half-difference.
--
--   ```lean
--   theorem OracleRealizationGap.mid_sq(hp : Odd p) (hq : Odd q) (hpq : p ≤ q) :
--       (mid p q) ^ 2 = p * q + ((q - p) / 2) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OracleRealizationGap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OracleRealizationGap.lean#L129

-- Thm stub generated from Novelty/OracleRealizationGap.lean
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap

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





variable {p q : ℕ}

theorem OracleRealizationGap.mid_sq(hp : Odd p) (hq : Odd q) (hpq : p ≤ q) :
    (mid p q) ^ 2 = p * q + ((q - p) / 2) ^ 2 := by sorry
