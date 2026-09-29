-- Prove2me | solution 1 for RateDial.mixture_family_eq_ray
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:39:38.38885+00:00
-- url     : https://prove2.me/submissions/0ff45bc9-5276-42db-9a94-f0a129109324

-- Sol generated from Shared/MixtureRateDialBaseline.lean
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





/-- **Collapse.**  Under flat composition every mixture is a scalar multiple of
the single common shape: the `|C|` rate parameters buy exactly one number. -/
theorem mixPred_eq_smul {S : C → ℝ → ℝ} {w : C → ℝ} {B : ℝ → ℝ}
    (hflat : FlatComposition S w B) (κ : C → ℝ) (t : ℝ) :
    mixPred κ S t = (∑ c, κ c * w c) * B t := by
  rw [mixPred, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by rw [hflat c t]; ring



/-! ## The residual is unchanged: removal is exactly zero -/







/-! ## Robust version: composition flat only up to a relative drift `δ` -/




/-! ## The registered verdict, with the measured numbers -/





/-! ## Capstone: the actual divisibility grid of `j² - N` -/






open RateDial in
theorem solution[DecidableEq C] {S : C → ℝ → ℝ} {w : C → ℝ} {B : ℝ → ℝ}
    (hflat : FlatComposition S w B) {c₀ : C} (hc₀ : w c₀ ≠ 0) :
    {f : ℝ → ℝ | ∃ κ : C → ℝ, mixPred κ S = f} = {f : ℝ → ℝ | ∃ K : ℝ, f = fun t => K * B t} := by
  ext f
  constructor
  · rintro ⟨κ, rfl⟩
    exact ⟨∑ c, κ c * w c, funext fun t => mixPred_eq_smul hflat κ t⟩
  · rintro ⟨K, rfl⟩
    refine ⟨fun c => if c = c₀ then K / w c₀ else 0, funext fun t => ?_⟩
    rw [mixPred_eq_smul hflat]
    have hsum : (∑ c, (if c = c₀ then K / w c₀ else 0) * w c) = K := by
      rw [Finset.sum_eq_single c₀]
      · rw [if_pos rfl]
        field_simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ c₀) h
    rw [hsum]
