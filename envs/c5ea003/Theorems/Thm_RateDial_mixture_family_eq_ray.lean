-- Prove2me | Theorems.Thm_RateDial_mixture_family_eq_ray
-- name    : RateDial.mixture_family_eq_ray
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:58.241985+00:00
-- url     : https://prove2.me/theorems/c4da4e64-8bfc-4a40-a619-09d6af9e1b70
-- title:
--   The mixture family is a ray.
-- statement:
--   **The mixture family is a ray.**  If some cell has a nonzero share, the set
--   of achievable predictions is exactly `{K Â· B : K â â}` â one rate dial, no
--   positional dial.
--
--   ```lean
--   theorem RateDial.mixture_family_eq_ray[DecidableEq C] {S : C → ℝ → ℝ} {w : C → ℝ} {B : ℝ → ℝ}
--       (hflat : FlatComposition S w B) {c₀ : C} (hc₀ : w c₀ ≠ 0) :
--       {f : ℝ → ℝ | ∃ κ : C → ℝ, mixPred κ S = f} = {f : ℝ → ℝ | ∃ K : ℝ, f = fun t => K * B t} := by sorry
--   /-! ## The residual is unchanged: removal is exactly zero -/
--
--
--
--
--
--
--
--   /-! ## Robust version: composition flat only up to a relative drift `δ` -/
--
--
--
--
--   /-! ## The registered verdict, with the measured numbers -/
--
--
--
--
--
--   /-! ## Capstone: the actual divisibility grid of `j² - N` -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/MixtureRateDialBaseline.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/MixtureRateDialBaseline.lean#L85

-- Thm stub generated from Shared/MixtureRateDialBaseline.lean
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells

/-!
# A flat-composition mixture baseline is a ray: it cannot absorb a positional excess (Part II)

Context: experiment 588c / paper 242.  A mid-window excess of the sieve hit
profile survived a `16`-cell divisibility mixture baseline
`PRED(t) = Σ_c κ_c · S_c(t)` with amplitude `0.1774 ± 0.0432` (`z = 4.11`) and
`0 %` removal relative to the single-`α` baseline.  Part I
(`Shared.MixtureRateDialCells`) proved the *structural* reason the mixture had no
positional freedom: the divisibility cell of `j² - N` is `210`-periodic in `j`,
so the class composition of a window is exactly the same wherever the window is.

This file proves the *algebraic* consequence — the theorem behind the slogan
**"divisibility is a rate dial, not a position dial"**.

* `mixPred_eq_smul` — flat composition collapses the whole `|C|`-parameter
  mixture family to a single scalar multiple of the common shape `B`.
* `mixture_family_eq_ray` — the set of achievable predictions is *exactly* the
  ray `{K · B}`; the mixture has one degree of freedom (a rate) and none in `t`.
* `mixPred_no_positional_freedom` — any two mixtures are proportional, pointwise
  in `t`.
* `relExcess_invariant`, `removal_eq_zero` — the residual's relative mid-window
  excess is *identical* to the one over the single-shape baseline: the removal
  fraction is exactly `0 %`, matching the measurement.
* `peak_position_invariant`, `argmax_invariant` — the peak stays at the same `t`.
* `mixture_cannot_fit_nonproportional` — if the measurement is not proportional
  to `B`, no mixture reproduces it.
* `mixPred_drift_bounds`, `excess_ratio_lower_bound_div` — the robust version:
  if composition is flat only up to a relative drift `δ`, the mixture can shrink
  the excess by at most the factor `(1-δ)/(1+δ)`.
* `absorption_requires_drift`, `drift_budget_measured` — the inverse, scale-free
  reading: absorbing a relative excess `ρ - 1` needs composition drift at least
  `(ρ-1)/(ρ+1)`, i.e. `8.1 %` for the measured excess against a measured drift of
  `0.269 %`.
* `H0_excess_survives_measured`, `H0_excess_beats_bar` — the registered verdict
  with the measured numbers: with the measured drift `δ = 0.269 %` and raw
  excess `0.1774`, the mixture residual excess is still `≥ 0.1710`, far above the
  registered bar `2 · SE = 0.0864` (and above the null-calibrated scale as well).
* `divisibility_mixture_excess_survives` — the capstone, with the mixture built
  from the *actual* `210`-periodic cell populations of Part I.
-/

open RateDial

open Finset

variable {C : Type*} [Fintype C]

/-! ## Flat composition and the mixture prediction -/

theorem RateDial.mixture_family_eq_ray[DecidableEq C] {S : C → ℝ → ℝ} {w : C → ℝ} {B : ℝ → ℝ}
    (hflat : FlatComposition S w B) {c₀ : C} (hc₀ : w c₀ ≠ 0) :
    {f : ℝ → ℝ | ∃ κ : C → ℝ, mixPred κ S = f} = {f : ℝ → ℝ | ∃ K : ℝ, f = fun t => K * B t} := by sorry
