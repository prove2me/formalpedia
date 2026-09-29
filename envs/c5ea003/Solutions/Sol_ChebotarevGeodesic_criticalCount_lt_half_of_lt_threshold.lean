-- Prove2me | solution 1 for ChebotarevGeodesic.criticalCount_lt_half_of_lt_threshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:48:52.45005+00:00
-- url     : https://prove2.me/submissions/3e83de55-491a-4b11-b4f4-f1989689559a

-- Sol generated from Shared/ChebotarevGeodesicThresholdSharp.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicThresholdSharp
/-
# Sharpness of the effective (Linnik-type) threshold

Continuation of `Shared.ChebotarevGeodesicEffective`, which proves

  `effective_lower_bound` : `π x ≥ (c/2)·x^β` for every `x ≥ max X₁ ((2C/c)^{2/(β-θ)})`

from the two hypotheses `|π - M| ≤ C x^{(θ+β)/2}` and `M x ≥ c x^β`.  Conjecture C3 of
`FUTURE_DIRECTIONS.md` asks whether the explicit threshold `(2C/c)^{2/(β-θ)}` is the true one.
It is: this file exhibits, for arbitrary admissible data `(c, C, θ, β)`, the extremal counting
function

  `criticalCount c C θ β x = c·x^β - C·x^{(θ+β)/2}`

for which the hypotheses hold with *equality*, and shows

* `criticalCount_error` : the error is exactly `C·x^{(θ+β)/2}`, so the data are admissible;
* `criticalCount_lt_half_of_lt_threshold` : *below* the threshold the conclusion **fails**
  everywhere, `π x < (c/2)·x^β`;
* `criticalCount_at_threshold` : *at* the threshold the conclusion holds with equality;
* `effective_threshold_sharp` : the packaged statement — the threshold of
  `effective_lower_bound` is attained and cannot be decreased;
* `effective_threshold_sharp_25_36` : the numerical instance of the paper, in which the
  least-geodesic threshold has the exact shape `(2C/c)^{72/11}`.
-/


open Filter
open scoped Topology

open ChebotarevGeodesic



/-- The threshold value `(2C/c)^{2/(β-θ)}` raised to the power `(β-θ)/2` is exactly `2C/c`. -/
theorem threshold_rpow {c C θ β : ℝ} (hc : 0 < c) (hC : 0 < C) (hθβ : θ < β) :
    ((2 * C / c) ^ (2 / (β - θ))) ^ ((β - θ) / 2) = 2 * C / c := by
  have hA : (0 : ℝ) < 2 * C / c := by positivity
  have hne : β - θ ≠ 0 := ne_of_gt (by linarith)
  rw [← Real.rpow_mul hA.le]
  rw [show 2 / (β - θ) * ((β - θ) / 2) = 1 by field_simp]
  exact Real.rpow_one _






open ChebotarevGeodesic in
theorem solution{c C θ β x : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hθβ : θ < β) (hx : 0 < x) (hlt : x < (2 * C / c) ^ (2 / (β - θ))) :
    criticalCount c C θ β x < (c / 2) * x ^ β := by
  set δ : ℝ := (β - θ) / 2 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hmid : (0 : ℝ) < x ^ ((θ + β) / 2) := Real.rpow_pos_of_pos hx _
  have hsplit : x ^ β = x ^ ((θ + β) / 2) * x ^ δ := by
    rw [← Real.rpow_add hx]
    congr 1
    simp only [hδdef]; ring
  have hxδ : x ^ δ < 2 * C / c := by
    have h := Real.rpow_lt_rpow hx.le hlt hδ
    rwa [threshold_rpow hc hC hθβ] at h
  have hkey : (c / 2) * x ^ β < C * x ^ ((θ + β) / 2) := by
    rw [hsplit]
    calc (c / 2) * (x ^ ((θ + β) / 2) * x ^ δ)
        = (c / 2) * x ^ δ * x ^ ((θ + β) / 2) := by ring
      _ < (c / 2) * (2 * C / c) * x ^ ((θ + β) / 2) := by
          have hmul : (c / 2) * x ^ δ < (c / 2) * (2 * C / c) :=
            mul_lt_mul_of_pos_left hxδ (by positivity)
          exact mul_lt_mul_of_pos_right hmul hmid
      _ = C * x ^ ((θ + β) / 2) := by field_simp
  rw [criticalCount]
  linarith
