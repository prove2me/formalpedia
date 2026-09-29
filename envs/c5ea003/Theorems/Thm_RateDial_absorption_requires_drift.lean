-- Prove2me | Theorems.Thm_RateDial_absorption_requires_drift
-- name    : RateDial.absorption_requires_drift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:57.350978+00:00
-- url     : https://prove2.me/theorems/ffdd434a-6af0-479c-933a-6f17308b8d46
-- title:
--   Drift budget (inverse form).
-- statement:
--   **Drift budget (inverse form).**  A mixture can only absorb the excess
--   entirely if its composition drift is at least `(Ï - 1)/(Ï + 1)`, where `Ï` is the
--   raw excess ratio.  This is a scale-free necessary condition: it does not mention
--   the data geometry, so it transfers across bit lengths unchanged.
--
--   ```lean
--   theorem RateDial.absorption_requires_drift{T0 T1 P0 P1 B0 B1 K δ ρ : ℝ}
--       (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB0 : 0 < B0) (hB1 : 0 < B1)
--       (hT0 : 0 ≤ T0) (hT1 : 0 < T1) (hP0 : 0 < P0) (hP1 : 0 < P1)
--       (hP0le : P0 ≤ (1 + δ) * (K * B0)) (hP1ge : (1 - δ) * (K * B1) ≤ P1)
--       (hρ : T0 * B1 = ρ * (T1 * B0))
--       (habs : (T0 / P0) / (T1 / P1) ≤ 1) :
--       (ρ - 1) / (ρ + 1) ≤ δ := by sorry
--
--   /-! ## Capstone: the actual divisibility grid of `j² - N` -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/MixtureRateDialBaseline.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/MixtureRateDialBaseline.lean#L276

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








/-! ## The residual is unchanged: removal is exactly zero -/







/-! ## Robust version: composition flat only up to a relative drift `δ` -/




/-! ## The registered verdict, with the measured numbers -/

theorem RateDial.absorption_requires_drift{T0 T1 P0 P1 B0 B1 K δ ρ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hT0 : 0 ≤ T0) (hT1 : 0 < T1) (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hP0le : P0 ≤ (1 + δ) * (K * B0)) (hP1ge : (1 - δ) * (K * B1) ≤ P1)
    (hρ : T0 * B1 = ρ * (T1 * B0))
    (habs : (T0 / P0) / (T1 / P1) ≤ 1) :
    (ρ - 1) / (ρ + 1) ≤ δ := by sorry
