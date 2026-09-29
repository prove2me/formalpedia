-- Prove2me | solution 1 for GeneratorTilt.integral_zGen
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:59:29.6742+00:00
-- url     : https://prove2.me/submissions/b4b4b702-0dd6-44ed-97ae-15cb737155bb

-- Sol generated from Novelty/GeneratorTiltWindowDesign.lean
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltRatio
import Definitions.Def_Novelty_GeneratorTiltWindowDesign
/-
# Can a different window rescue the ascending scan?  A no-go theorem

Cycle 1 (`Novelty.GeneratorTiltRatio`) fixed the *canonical* window `(√(N/2), √N]`, whose
multiplier is `R = 2`, and found the tie ratio `r★ = 24 - 16√2 ≈ 1.3726`.  The obvious
follow-up is a design question: the window multiplier is a free parameter — scanning
`(√(N/R), √N]` upwards is well defined whenever the generator guarantees `q < R p` — so can
a *wider* (or narrower) window make the ascending order win on the near-balanced populations
that deployed generators actually produce?

This file answers **no**, quantitatively.  For the `R`-window the tilt law is
`zGen R r = (r^{-1/2} - R^{-1/2}) / (1 - R^{-1/2})`, and:

* `zGen_criticalRatioGen`, `half_lt_zGen_iff` — the tie ratio for multiplier `R` is exactly
  `r★(R) = 4R / (1 + √R)²`, and ratios below it are top-heavy (ascending loses);
* `one_lt_criticalRatioGen` — `r★(R) > 1` for **every** `R > 1`: whatever the window, an
  interval of ratios just above `1` is adversarial to the ascending scan.  Since real
  generators concentrate the ratio near `1`, no window design removes the adversarial tilt;
* `criticalRatioGen_lt_four` — moreover `r★(R) < 4` for every `R`: the tie point can never be
  pushed past ratio `4`, so the "widen the window" strategy is capped;
* `integral_zGen` / `mean_zGen_uniform` — the exact mean tilt of a *ratio-uniform* pool on
  `[1, R]` is `1/(1 + √R)`, always `< 1/2`.  Artificial ratio-uniform pools are bottom-heavy
  for every window multiplier, which is precisely why they are the only place a
  window-ascending advantage was ever seen.  (At `R = 2` this recovers `√2 - 1`.)

Taken together with `Novelty.GeneratorTiltSynthesis`, the scope boundary is now closed on
both sides: bottom-heavy = artificial ratio-spread pools, top-heavy = near-balanced deployed
pools, for every admissible window.
-/

open GeneratorTilt

open Real




variable {R : ℝ}

theorem one_lt_sqrt (hR : 1 < R) : 1 < Real.sqrt R := by
  have : Real.sqrt 1 < Real.sqrt R := Real.sqrt_lt_sqrt (by norm_num) hR
  simpa using this

theorem sqrt_sq_self (hR : 1 < R) : Real.sqrt R * Real.sqrt R = R :=
  Real.mul_self_sqrt (by linarith)

theorem one_sub_inv_sqrt_pos (hR : 1 < R) : 0 < 1 - 1 / Real.sqrt R := by
  have h := one_lt_sqrt hR
  rw [sub_pos, div_lt_one (by linarith)]
  exact h

/-! ## Values, monotonicity, the tie ratio -/







/-! ## The no-go bounds on the tie ratio -/





/-! ## Ratio-uniform pools are bottom-heavy for every window -/

theorem integral_one_div_sqrt_gen (hR : 1 < R) :
    ∫ r in (1:ℝ)..R, 1 / Real.sqrt r = 2 * Real.sqrt R - 2 := by
  have h : ∀ r ∈ Set.uIcc (1:ℝ) R, 1 / Real.sqrt r = r ^ (-(1:ℝ)/2) := by
    intro r hr
    rw [Set.uIcc_of_le (by linarith)] at hr
    have hr0 : (0:ℝ) ≤ r := le_trans (by norm_num) hr.1
    rw [show -(1:ℝ)/2 = -(1/2) by ring, Real.rpow_neg hr0, ← Real.sqrt_eq_rpow, one_div]
  rw [intervalIntegral.integral_congr h, integral_rpow (by left; norm_num),
    show -(1:ℝ)/2 + 1 = 1/2 by ring, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_one]
  ring

theorem intervalIntegrable_one_div_sqrt_gen (hR : 1 < R) :
    IntervalIntegrable (fun r : ℝ => 1 / Real.sqrt r) MeasureTheory.volume 1 R := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
  intro x hx
  rw [Set.uIcc_of_le (by linarith)] at hx
  exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))







open GeneratorTilt in
theorem solution(hR : 1 < R) :
    (∫ r in (1:ℝ)..R, zGen R r) = (R - 1) / (1 + Real.sqrt R) := by
  have hs := one_lt_sqrt hR
  have h2 := sqrt_sq_self hR
  have hd := one_sub_inv_sqrt_pos hR
  have hne : Real.sqrt R - 1 ≠ 0 := by linarith
  have hne0 : Real.sqrt R ≠ 0 := by linarith
  have hfun : ∀ r ∈ Set.uIcc (1:ℝ) R, zGen R r
      = (1 - 1 / Real.sqrt R)⁻¹ * (1 / Real.sqrt r)
        - (1 / Real.sqrt R) / (1 - 1 / Real.sqrt R) := by
    intro r _
    unfold zGen
    field_simp
  rw [intervalIntegral.integral_congr hfun,
    intervalIntegral.integral_sub ((intervalIntegrable_one_div_sqrt_gen hR).const_mul _)
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_one_div_sqrt_gen hR,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  nlinarith [h2, hs]
