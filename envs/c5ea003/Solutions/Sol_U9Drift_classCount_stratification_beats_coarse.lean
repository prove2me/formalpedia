-- Prove2me | solution 1 for U9Drift.classCount_stratification_beats_coarse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:47:37.701509+00:00
-- url     : https://prove2.me/submissions/e94fc6fa-2cbb-4779-af75-430fd5f21c0b

-- Sol generated from Probability/U9DriftStratification.lean
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
import Definitions.Def_Probability_U9DriftStratification
import Theorems.Thm_U9Drift_strat_ss_decomposition
import Theorems.Thm_U9Drift_totalSS_signProd
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
theorem solution(k : ℕ) (hk : 1 ≤ k) :
    betweenSS (fun e : Fin k → Bool => signProd e) (fun _ => (0 : ℕ)) {0} = 0 ∧
    0 < withinSS (fun e : Fin k → Bool => signProd e) (fun _ => (0 : ℕ)) {0} := by
  have hK : ∀ e : Fin k → Bool, (fun _ => (0 : ℕ)) e ∈ ({0} : Finset ℕ) := by simp
  have hfib : fiber (fun _ : Fin k → Bool => (0 : ℕ)) 0 = univ := by
    ext e; simp [fiber]
  have hmean : fiberMean (fun e : Fin k → Bool => signProd e) (fun _ => (0 : ℕ)) 0
      = popMean (fun e : Fin k → Bool => signProd e) := by
    rw [fiberMean, popMean, hfib]
    congr 1
  have hbet : betweenSS (fun e : Fin k → Bool => signProd e) (fun _ => (0 : ℕ)) {0} = 0 := by
    rw [betweenSS]
    simp [hmean]
  refine ⟨hbet, ?_⟩
  have hdec := strat_ss_decomposition (fun e : Fin k → Bool => signProd e)
    (fun _ => (0 : ℕ)) {0} hK
  have htot : totalSS (fun e : Fin k → Bool => signProd e) = 2 ^ k * (2 ^ k - 1) :=
    totalSS_signProd k
  have hpos : (0 : ℚ) < 2 ^ k * (2 ^ k - 1) := by
    have h2 : (2 : ℚ) ^ 1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h1 : (0 : ℚ) < 2 ^ k - 1 := by
      have : (2 : ℚ) ^ 1 = 2 := by norm_num
      linarith [h2, this.symm.le]
    have h0 : (0 : ℚ) < 2 ^ k := by positivity
    exact mul_pos h0 h1
  rw [htot, hbet, add_zero] at hdec
  linarith [hdec, hpos]
