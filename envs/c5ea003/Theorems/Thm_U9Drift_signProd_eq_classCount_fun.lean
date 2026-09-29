-- Prove2me | Theorems.Thm_U9Drift_signProd_eq_classCount_fun
-- name    : U9Drift.signProd_eq_classCount_fun
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:23:09.785689+00:00
-- url     : https://prove2.me/theorems/2fb10911-11d7-473a-849d-210de3c9503d
-- title:
--   The bias is a function of the quadratic-class count alone: this is exactly the
-- statement:
--   The bias is a function of the quadratic-class count alone: this is exactly the
--   statistic sub-conjecture **A** proposed to stratify on.
--
--   ```lean
--   theorem U9Drift.signProd_eq_classCount_fun{k : ℕ} (e : Fin k → Bool) :
--       signProd e = if classCount e = k then (2 : ℚ) ^ k else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftStratification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftStratification.lean#L203

-- Thm stub generated from Probability/U9DriftStratification.lean
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

theorem U9Drift.signProd_eq_classCount_fun{k : ℕ} (e : Fin k → Bool) :
    signProd e = if classCount e = k then (2 : ℚ) ^ k else 0 := by sorry
