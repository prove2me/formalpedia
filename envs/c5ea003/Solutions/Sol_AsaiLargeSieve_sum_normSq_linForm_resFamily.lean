-- Prove2me | solution 1 for AsaiLargeSieve.sum_normSq_linForm_resFamily
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:10:32.728419+00:00
-- url     : https://prove2.me/submissions/cb366e3c-bd0e-497d-a02f-9758bac0a958

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
theorem solution{q : ℕ} (hq : 0 < q) {D : ℝ} (hD : 0 ≤ D) (N : ℕ) :
    ∑ f ∈ Finset.range q, ‖linForm (resFamily q D) N (resIndicator q) f‖ ^ 2
      = D * (((Finset.range N).filter (fun n => n % q = 0)).card : ℝ) ^ 2 := by
  classical
  set K := ((Finset.range N).filter (fun n => n % q = 0)).card with hK
  have hzero : (0 : ℕ) ∈ Finset.range q := Finset.mem_range.mpr hq
  have hf0 : linForm (resFamily q D) N (resIndicator q) 0
      = ((Real.sqrt D : ℝ) : ℂ) * (K : ℂ) := by
    rw [linForm]
    have hpt : ∀ n ∈ Finset.range N,
        resIndicator q n * resFamily q D 0 n
          = if n % q = 0 then ((Real.sqrt D : ℝ) : ℂ) else 0 := by
      intro n _
      by_cases h : n % q = 0 <;> simp [resIndicator, resFamily, h]
    rw [Finset.sum_congr rfl hpt]
    simp [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, hK, mul_comm]
  have hfne : ∀ f ∈ Finset.range q, f ≠ 0 →
      linForm (resFamily q D) N (resIndicator q) f = 0 := by
    intro f _ hf
    rw [linForm]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases h : n % q = 0
    · have : n % q ≠ f := by rw [h]; exact fun hc => hf hc.symm
      simp [resFamily, this]
    · simp [resIndicator, h]
  have hsum : ∑ f ∈ Finset.range q, ‖linForm (resFamily q D) N (resIndicator q) f‖ ^ 2
      = ‖linForm (resFamily q D) N (resIndicator q) 0‖ ^ 2 := by
    refine Finset.sum_eq_single 0 (fun f hf hne => ?_) (fun hcon => absurd hzero hcon)
    rw [hfne f hf hne, norm_zero]
    norm_num
  rw [hsum, hf0, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg D), Real.sq_sqrt hD]
  simp
