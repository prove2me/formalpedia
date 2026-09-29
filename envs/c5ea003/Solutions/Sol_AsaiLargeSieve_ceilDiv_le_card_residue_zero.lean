-- Prove2me | solution 1 for AsaiLargeSieve.ceilDiv_le_card_residue_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:01:09.206178+00:00
-- url     : https://prove2.me/submissions/d40a3376-c4af-4f60-9147-0d15426495de

-- Sol generated from Novelty/AsaiPeriodicOptimal.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiPeriodicOptimal
/-
# The periodic large sieve constant is exactly `D · ⌈N/q⌉`

This file continues the formalisation of the analytic skeleton of the paper
**"On the Second Moment of `L(1/2, As(f) × φ)`"** (`Novelty.AsaiLargeSieve`,
`Novelty.AsaiLargeSieveGram`, `Novelty.AsaiSecondMoment`, `Novelty.AsaiMomentApplications`,
`Novelty.AsaiLargeSieveSharp`, `Novelty.AsaiSecondMomentLower`,
`Novelty.AsaiOverlapMultiplicity`).  It settles conjecture **C7** of `FUTURE_DIRECTIONS.md`.

`AsaiLargeSieve.largeSieve_of_periodic_gram_ceil` shows that a `q`-periodic Gram matrix with
entries bounded by `D` admits the large sieve constant `D · ⌈N/q⌉`.  C7 asserted that this
constant is *optimal*: no smaller one is admissible for the extremal periodic family.  That
is proved here.

## Contents

* `AsaiLargeSieve.resFamily` — the extremal `q`-periodic family
  `lam f n = √D · 1_{n ≡ f (mod q)}`, indexed by the residues `f < q`.  Its Gram matrix is
  computed exactly in `gram_resFamily`: it is `D` on `m ≡ n (mod q)` and `0` elsewhere, i.e.
  precisely the extremal matrix allowed by the hypotheses of the periodic criterion.
* `AsaiLargeSieve.largeSieve_resFamily` — the upper bound, an instance of the periodic
  criterion.
* `AsaiLargeSieve.le_of_largeSieve_resFamily` — the matching **lower** bound: every
  admissible constant `C` for this family satisfies `D · ⌈N/q⌉ ≤ C`.  The extremal test
  vector is the indicator of the residue class of `0`, which meets `[0,N)` in at least
  `⌈N/q⌉ = (N + q - 1)/q` points (`ceilDiv_le_card_residue_zero`), and on which the quadratic
  form takes the value `D · k²` against a coefficient mass `k`
  (`sum_normSq_linForm_resFamily`, `sum_normSq_resIndicator`).
* `AsaiLargeSieve.isLeast_periodic_constant` — the two halves combined: `D · ⌈N/q⌉` is the
  *least* admissible large sieve constant for `resFamily`.  In particular the criterion
  `largeSieve_of_periodic_gram_ceil` cannot be improved, and — by
  `ceilDiv_lt_real_of_not_dvd` — the older constant `D · (N/q + 1)` is genuinely
  suboptimal whenever `q ∤ N`.
* `AsaiLargeSieve.periodic_saving` — the quantitative gain over the trivial constant: for the
  extremal family the trivial (Cauchy–Schwarz) constant is `D · N`, so the periodic criterion
  saves a factor of essentially `q`.
-/

open Finset Complex

open AsaiLargeSieve












open AsaiLargeSieve in
theorem solution{q : ℕ} (hq : 0 < q) (N : ℕ) :
    (N + q - 1) / q ≤ ((Finset.range N).filter (fun n => n % q = 0)).card := by
  classical
  set k := (N + q - 1) / q with hk
  have hkq : k * q ≤ N + q - 1 := Nat.div_mul_le_self _ _
  have hmap : ∀ i ∈ Finset.range k, i * q ∈ (Finset.range N).filter (fun n => n % q = 0) := by
    intro i hi
    have hik : i + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have h1 : (i + 1) * q ≤ k * q := Nat.mul_le_mul_right q hik
    have h2 : i * q < N := by
      have : (i + 1) * q = i * q + q := by ring
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, ?_⟩
    simp [Nat.mul_mod_left]
  have hinj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i * q = j * q → i = j := by
    intro i _ j _ h
    exact Nat.eq_of_mul_eq_mul_right hq h
  have hcard : (Finset.range k).card
      ≤ ((Finset.range N).filter (fun n => n % q = 0)).card := by
    refine Finset.card_le_card_of_injOn (fun i => i * q) (fun i hi => hmap i hi) ?_
    intro i hi j hj h
    exact hinj i (by simpa using hi) j (by simpa using hj) h
  simpa using hcard
