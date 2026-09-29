-- Prove2me | solution 1 for U9Drift.withinSS_eq_zero_of_fiberwise_constant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:34:28.52006+00:00
-- url     : https://prove2.me/submissions/438d397c-e061-425d-b604-9581313b5ed5

-- Sol generated from Probability/U9DriftStratification.lean
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
import Definitions.Def_Probability_U9DriftStratification
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Stratifying the band-9 moduli by quadratic class: an exact variance accounting

Context (experiment 569, paper 216).  `Catalog/Probability/U9DriftLocalDensity.lean` shows
that the multiplicative bias of one modulus across `k` small primes,
`signProd e = ∏ i, (1 + ε i)` with `ε i = ±1` the quadratic characters, has mean `1` and
variance `2 ^ k - 1`: the between-modulus dispersion that forces the cluster bootstrap is
exponentially large.  Conjecture **C1** of `FUTURE_DIRECTIONS.md` (sub-conjecture **A**)
proposed to remove that dispersion by *stratifying* the moduli on the quadratic-class
statistic `∑_{p} χ_p(N)`, i.e. on the number of primes at which `N` is a residue.

This file closes the structural half of that conjecture.

* `U9Drift.strat_ss_decomposition` — the exact one-way ANOVA identity for an arbitrary
  finite population `Ω`, an arbitrary real-valued statistic `f` and an arbitrary
  stratifying map `key : Ω → κ`:
  `totalSS = withinSS + betweenSS`.  No balance assumption: fibres may have any sizes,
  including zero.
* `U9Drift.withinSS_le_totalSS` — hence stratification never increases the residual
  dispersion, and `U9Drift.betweenSS_le_totalSS`.
* `U9Drift.withinSS_eq_zero_of_fiberwise_constant` /
  `U9Drift.betweenSS_eq_totalSS_of_fiberwise_constant` — a statistic that is a function of
  the stratum key has *no* within-stratum dispersion at all.
* `U9Drift.signProd_eq_ite` and `U9Drift.signProd_eq_of_classCount_eq` — the multiplicative
  bias is a function of the quadratic-class count `classCount e = #{i | ε i = +1}` alone.
* `U9Drift.totalSS_signProd` — the population sum of squares of the bias is exactly
  `2 ^ k * (2 ^ k - 1)`, matching `variance_signProd`.
* `U9Drift.classCount_stratification_is_exact` — **the conjecture, proved**: stratifying by
  the quadratic-class count leaves zero within-stratum dispersion, so it accounts for the
  entire `2 ^ k - 1` between-modulus variance.
* `U9Drift.classCount_stratification_beats_coarse` — the accounting is not vacuous: the
  trivial (single-stratum) design leaves *all* of the dispersion unexplained, and for
  `k ≥ 1` that is a strictly positive amount.
-/

open U9Drift

open Finset


variable {Ω : Type*} [Fintype Ω] {κ : Type*} [DecidableEq κ]
















/-! ## Application: the quadratic-class stratification of the multiplicative bias -/











open U9Drift in
theorem solution(f : Ω → ℚ) (key : Ω → κ) (K : Finset κ)
    (g : κ → ℚ) (hg : ∀ x, f x = g (key x)) : withinSS f key K = 0 := by
  refine Finset.sum_eq_zero fun c _ => ?_
  have hval : ∀ x ∈ fiber key c, f x = g c := by
    intro x hx
    have : key x = c := by simpa [fiber] using hx
    rw [hg x, this]
  rcases Finset.eq_empty_or_nonempty (fiber key c) with he | hne
  · simp [he]
  · have hcard : ((fiber key c).card : ℚ) ≠ 0 := by
      have : 0 < (fiber key c).card := Finset.card_pos.mpr hne
      positivity
    have hsum : ∑ x ∈ fiber key c, f x = (fiber key c).card * g c := by
      rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    have hmean : fiberMean f key c = g c := by
      rw [fiberMean, hsum]
      field_simp
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hmean, hval x hx]
    ring
