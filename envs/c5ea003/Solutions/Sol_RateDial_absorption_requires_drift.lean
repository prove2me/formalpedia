-- Prove2me | solution 1 for RateDial.absorption_requires_drift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:38:01.995879+00:00
-- url     : https://prove2.me/submissions/1feaeee9-e310-47f0-baba-e926dd2bf63e

-- Sol generated from Shared/MixtureRateDialBaseline.lean
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells
import Theorems.Thm_RateDial_excess_ratio_lower_bound_mul

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



/-- Division form of the robustness estimate. -/
theorem excess_ratio_lower_bound_div {T0 T1 P0 P1 B0 B1 K δ ρ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hT0 : 0 ≤ T0) (hT1 : 0 < T1) (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hP0le : P0 ≤ (1 + δ) * (K * B0)) (hP1ge : (1 - δ) * (K * B1) ≤ P1)
    (hρ : T0 * B1 = ρ * (T1 * B0)) :
    ρ * (1 - δ) / (1 + δ) ≤ (T0 / P0) / (T1 / P1) := by
  have hmul := excess_ratio_lower_bound_mul (K := K) hδ0 hδ1 hB0 hB1 hT0 hT1 hP0le hP1ge hρ
  have hδpos : 0 < 1 + δ := by linarith
  have hkey : (T0 / P0) / (T1 / P1) = (T0 * P1) / (T1 * P0) := by
    field_simp
  rw [hkey]
  refine (div_le_div_iff₀ hδpos (mul_pos hT1 hP0)).mpr ?_
  nlinarith

/-! ## The registered verdict, with the measured numbers -/





/-! ## Capstone: the actual divisibility grid of `j² - N` -/






open RateDial in
theorem solution{T0 T1 P0 P1 B0 B1 K δ ρ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hB0 : 0 < B0) (hB1 : 0 < B1)
    (hT0 : 0 ≤ T0) (hT1 : 0 < T1) (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hP0le : P0 ≤ (1 + δ) * (K * B0)) (hP1ge : (1 - δ) * (K * B1) ≤ P1)
    (hρ : T0 * B1 = ρ * (T1 * B0))
    (habs : (T0 / P0) / (T1 / P1) ≤ 1) :
    (ρ - 1) / (ρ + 1) ≤ δ := by
  have hbound := excess_ratio_lower_bound_div (K := K) hδ0 hδ1 hB0 hB1 hT0 hT1 hP0 hP1
    hP0le hP1ge hρ
  have hρ0 : 0 ≤ ρ := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hT0 hB1.le, mul_pos hT1 hB0]
  have hδpos : 0 < 1 + δ := by linarith
  have hle : ρ * (1 - δ) / (1 + δ) ≤ 1 := le_trans hbound habs
  have hmul : ρ * (1 - δ) ≤ 1 + δ := by
    rw [div_le_one hδpos] at hle
    linarith
  rw [div_le_iff₀ (by linarith : (0:ℝ) < ρ + 1)]
  nlinarith
