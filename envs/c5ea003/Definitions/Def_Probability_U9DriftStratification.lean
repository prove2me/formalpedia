-- Prove2me | Definitions.Def_Probability_U9DriftStratification
-- name    : Probability_U9DriftStratification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:45.257878+00:00
-- url     : https://prove2.me/theorems/c0550586-05a7-487f-b106-c617c2521b29
-- title:
--   Aether Catalog definitions — Probability_U9DriftStratification
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftStratification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftStratification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_U9DriftLocalDensity
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

namespace U9Drift

open Finset

section Stratification

variable {Ω : Type*} [Fintype Ω] {κ : Type*} [DecidableEq κ]

/-- The stratum (fibre) of the stratifying map `key` above the label `c`. -/
def fiber (key : Ω → κ) (c : κ) : Finset Ω := univ.filter (fun x => key x = c)

/-- The mean of `f` over the stratum `c` (`0` on an empty stratum). -/
def fiberMean (f : Ω → ℚ) (key : Ω → κ) (c : κ) : ℚ :=
  (∑ x ∈ fiber key c, f x) / (fiber key c).card

/-- The mean of `f` over the whole population (`0` on an empty population). -/
def popMean (f : Ω → ℚ) : ℚ := (∑ x, f x) / (Fintype.card Ω)

/-- Total sum of squares: dispersion of `f` about the population mean. -/
def totalSS (f : Ω → ℚ) : ℚ := ∑ x, (f x - popMean f) ^ 2

/-- Within-stratum sum of squares. -/
def withinSS (f : Ω → ℚ) (key : Ω → κ) (K : Finset κ) : ℚ :=
  ∑ c ∈ K, ∑ x ∈ fiber key c, (f x - fiberMean f key c) ^ 2

/-- Between-stratum sum of squares. -/
def betweenSS (f : Ω → ℚ) (key : Ω → κ) (K : Finset κ) : ℚ :=
  ∑ c ∈ K, (fiber key c).card * (fiberMean f key c - popMean f) ^ 2









end Stratification

/-! ## Application: the quadratic-class stratification of the multiplicative bias -/

/-- The quadratic-class count of a modulus: the number of small primes at which `N` is a
quadratic residue (`ε i = +1`, coded `e i = true`). -/
def classCount {k : ℕ} (e : Fin k → Bool) : ℕ := (univ.filter (fun i => e i = true)).card









end U9Drift


