-- Prove2me | solution 1 for ProfileForm.residualFit_ne_powerProfile
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:39:35.6702+00:00
-- url     : https://prove2.me/submissions/fa222757-7a98-4323-a320-ba42d534311d

-- Sol generated from NumberTheory/ProfileFormResidualPeak.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Theorems.Thm_ProfileForm_exists_interiorMax_of_gt_endpoints
import Theorems.Thm_ProfileForm_not_antitoneOn_of_peak
import Theorems.Thm_ProfileForm_not_monotoneOn_of_peak

/-!
# Profile form II: the mixture baseline absorbs the decline, the residual peaks

Context (experiment 579, paper 229; V2 rule).  After dividing the measured
small-`j` hit profile `T` by the mixture-Dickman baseline `M`, the residual
`R = T / M` is **not** monotone: the baseline absorbs almost all of the raw
decline (`M` falls `3.64x` where `T` falls `3.25x`) and what is left is a
concave mid-window hump, `±20 %`, with an interior vertex at `x ≈ 0.59` and end
deficits `0.80` (small-`j` wall) and `0.90`.

This file proves the two structural halves of that statement.

**Absorption.**  The mixture baseline is the uniform scale mixture of
exponential regimes,
`M x = ∫ s in 0..1, exp (-(x s)) = (1 - exp (-x)) / x`
(`dickmanMixtureBaseline_eq_mixtureIntegral`; the same mixture appears in the
catalog file `NumberTheory.ProofRegimeMixturePowerLaw`).  It is squeezed between
`1/(2x)` and `1/x` on `x ≥ 1` (`dickmanMixtureBaseline_bounds`), so the residual
`R = T / M` obeys `A x (1+x)^(-b) ≤ R x ≤ 2 A x (1+x)^(-b)`
(`residual_absorption_bounds`) and consequently declines across the window by a
factor at most `2/3` of the raw decline of `T`
(`residual_decline_le_two_thirds_raw`): the baseline really does eat the
harmonic gradient, whatever the exponent is.

**Peakedness.**  A profile that is strictly larger at an interior point than at
both ends attains its maximum in the interior and is neither monotone nor
antitone (`exists_interiorMax_of_gt_endpoints`, `not_monotoneOn_of_peak`,
`not_antitoneOn_of_peak`).  The fitted quadratic residual
`R̂(x) = 4/5 + (59/90) x - (5/9) x²` — the concave fit with the measured end
values `0.80`, `0.90` and vertex `0.59` — satisfies exactly that
(`residualFit_peak`), with hump ratios `≥ 6/5` over the left end and `≥ 11/10`
over the right end (`residualFit_hump_ratio_left`, `..._right`).

**Consequence.**  Power-law profiles are monotone on the window
(`powerProfile_antitoneOn`, `powerProfile_monotoneOn`), so the residual is *not*
of profile form (`residualFit_ne_powerProfile`); equivalently, an interior peak
in `T / M` forces `M` to be *not* a power-law rescaling of `T`
(`peak_forces_nonPowerLaw_baseline`).  The two layers are therefore separate:
the profile layer has a law, the residual layer is a genuinely new object.
-/

open ProfileForm

open Real Set

/-! ## The mixture-Dickman baseline -/





/-! ## Absorption: the baseline eats the harmonic gradient -/




/-! ## Peakedness: a general criterion -/




/-! ## The fitted residual: a concave interior hump -/





/-- Exact concavity identity: the deficit from the vertex is a perfect square. -/
theorem residualFit_vertex_identity (x : ℝ) :
    residualFit (59/100) - residualFit x = (5/9) * (x - 59/100) ^ 2 := by
  simp only [residualFit]; ring

/-- The vertex is the strict global maximum. -/
theorem residualFit_lt_vertex {x : ℝ} (hx : x ≠ 59/100) :
    residualFit x < residualFit (59/100) := by
  have h := residualFit_vertex_identity x
  have hsq : 0 < (x - 59/100) ^ 2 := by
    have : x - 59/100 ≠ 0 := sub_ne_zero.mpr hx
    positivity
  nlinarith





/-- **The residual is peaked, not monotone.** -/
theorem residualFit_peak :
    (∃ m ∈ Ioo (0:ℝ) 1, IsMaxOn residualFit (Icc (0:ℝ) 1) m) ∧
      ¬ MonotoneOn residualFit (Icc (0:ℝ) 1) ∧
      ¬ AntitoneOn residualFit (Icc (0:ℝ) 1) := by
  have hc : (59/100 : ℝ) ∈ Ioo (0:ℝ) 1 := by constructor <;> norm_num
  have h0 : residualFit 0 < residualFit (59/100) := residualFit_lt_vertex (by norm_num)
  have h1 : residualFit 1 < residualFit (59/100) := residualFit_lt_vertex (by norm_num)
  have hcont : ContinuousOn residualFit (Icc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    unfold residualFit
    fun_prop
  exact ⟨exists_interiorMax_of_gt_endpoints hcont hc h0 h1,
    not_monotoneOn_of_peak hc h1, not_antitoneOn_of_peak hc h0⟩

/-! ## The residual is not of profile form -/

theorem powerProfile_antitoneOn {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b) :
    AntitoneOn (powerProfile A b) (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : (0:ℝ) < 1 + x := by have := hx.1; linarith
  simp only [powerProfile]
  apply mul_le_mul_of_nonneg_left _ hA.le
  exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)

theorem powerProfile_monotoneOn {A b : ℝ} (hA : 0 < A) (hb : b ≤ 0) :
    MonotoneOn (powerProfile A b) (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : (0:ℝ) < 1 + x := by have := hx.1; linarith
  simp only [powerProfile]
  apply mul_le_mul_of_nonneg_left _ hA.le
  exact Real.rpow_le_rpow hx0.le (by linarith) (by linarith)




theorem solution{A b : ℝ} (hA : 0 < A) :
    ¬ ∀ x ∈ Icc (0:ℝ) 1, residualFit x = powerProfile A b x := by
  intro h
  have hpeak := residualFit_peak
  rcases le_or_gt 0 b with hb | hb
  · refine hpeak.2.2 ?_
    intro x hx y hy hxy
    rw [h x hx, h y hy]
    exact powerProfile_antitoneOn hA hb hx hy hxy
  · refine hpeak.2.1 ?_
    intro x hx y hy hxy
    rw [h x hx, h y hy]
    exact powerProfile_monotoneOn hA hb.le hx hy hxy
