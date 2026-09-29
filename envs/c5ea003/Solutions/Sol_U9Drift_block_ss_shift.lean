-- Prove2me | solution 1 for U9Drift.block_ss_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:23:12.915345+00:00
-- url     : https://prove2.me/submissions/68336448-3f81-49c5-99c5-c93656c0d77c

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
omit [Fintype Ω] in
theorem solution(F : Finset Ω) (f : Ω → ℚ) (m : ℚ) :
    ∑ x ∈ F, (f x - m) ^ 2
      = (∑ x ∈ F, (f x - (∑ y ∈ F, f y) / F.card) ^ 2)
        + F.card * ((∑ y ∈ F, f y) / F.card - m) ^ 2 := by
  set mF : ℚ := (∑ y ∈ F, f y) / F.card with hmF
  have hcenter : ∑ x ∈ F, (f x - mF) = 0 := by
    rcases Nat.eq_zero_or_pos F.card with h0 | hpos
    · simp [Finset.card_eq_zero.mp h0]
    · have hne : (F.card : ℚ) ≠ 0 := by positivity
      rw [Finset.sum_sub_distrib]
      rw [Finset.sum_const, nsmul_eq_mul, hmF]
      field_simp
      ring
  have hexp : ∀ x ∈ F, (f x - m) ^ 2
      = (f x - mF) ^ 2 + 2 * (mF - m) * (f x - mF) + (mF - m) ^ 2 := by
    intro x _
    ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcenter,
    Finset.sum_const, nsmul_eq_mul]
  ring
