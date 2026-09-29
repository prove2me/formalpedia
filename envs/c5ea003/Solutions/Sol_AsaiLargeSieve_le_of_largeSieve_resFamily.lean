-- Prove2me | solution 1 for AsaiLargeSieve.le_of_largeSieve_resFamily
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:15:40.481634+00:00
-- url     : https://prove2.me/submissions/17a23bed-c76a-4edd-bc1f-4aad0656e801

-- Sol generated from Novelty/AsaiPeriodicOptimal.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiPeriodicOptimal
import Theorems.Thm_AsaiLargeSieve_ceilDiv_le_card_residue_zero
import Theorems.Thm_AsaiLargeSieve_sum_normSq_linForm_resFamily
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






/-- The coefficient mass of the extremal test vector is the size of the residue class. -/
theorem sum_normSq_resIndicator (q N : ℕ) :
    ∑ n ∈ Finset.range N, ‖resIndicator q n‖ ^ 2
      = (((Finset.range N).filter (fun n => n % q = 0)).card : ℝ) := by
  classical
  simp [resIndicator, apply_ite (fun z : ℂ => ‖z‖ ^ 2)]






open AsaiLargeSieve in
theorem solution{q N : ℕ} (hq : 0 < q) (hN : 0 < N) {D : ℝ} (hD : 0 ≤ D)
    {C : ℝ} (h : LargeSieve (Finset.range q) (resFamily q D) N C) :
    D * (((N + q - 1) / q : ℕ) : ℝ) ≤ C := by
  classical
  set K := ((Finset.range N).filter (fun n => n % q = 0)).card with hK
  have hk1 : 1 ≤ (N + q - 1) / q := by
    have : q ≤ N + q - 1 := by omega
    exact (Nat.one_le_div_iff hq).mpr this
  have hKk : (N + q - 1) / q ≤ K := ceilDiv_le_card_residue_zero hq N
  have hKpos : 0 < K := lt_of_lt_of_le hk1 hKk
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have htest := h (resIndicator q)
  rw [sum_normSq_linForm_resFamily hq hD N, sum_normSq_resIndicator q N] at htest
  have hstep : D * (K : ℝ) ≤ C := by
    have : D * (K : ℝ) * (K : ℝ) ≤ C * (K : ℝ) := by nlinarith [htest]
    exact le_of_mul_le_mul_right this hKR
  have hcast : (((N + q - 1) / q : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKk
  calc D * (((N + q - 1) / q : ℕ) : ℝ) ≤ D * (K : ℝ) := mul_le_mul_of_nonneg_left hcast hD
    _ ≤ C := hstep
