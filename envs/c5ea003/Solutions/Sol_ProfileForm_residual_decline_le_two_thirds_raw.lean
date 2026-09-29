-- Prove2me | solution 1 for ProfileForm.residual_decline_le_two_thirds_raw
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:53:33.126766+00:00
-- url     : https://prove2.me/submissions/0fb29143-e684-4b1e-9ad4-e97d58860e86

-- Sol generated from NumberTheory/ProfileFormResidualPeak.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Theorems.Thm_ProfileForm_residual_absorption_bounds

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












/-! ## The residual is not of profile form -/






open ProfileForm in
theorem solution{A b : ℝ} (hA : 0 < A) :
    residual A b 1 / residual A b 3 ≤
      (2 / 3) * (powerProfile A b 1 / powerProfile A b 3) := by
  have h1 := residual_absorption_bounds (A := A) (b := b) (x := 1) hA le_rfl
  have h3 := residual_absorption_bounds (A := A) (b := b) (x := 3) hA (by norm_num)
  have hp1 : (0:ℝ) < (1 + (1:ℝ)) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hp3 : (0:ℝ) < (1 + (3:ℝ)) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hR3pos : 0 < residual A b 3 := by
    have : (0:ℝ) < A * 3 * (1 + 3) ^ (-b) := by positivity
    linarith [h3.1]
  have hR1le : residual A b 1 ≤ 2 * (A * 1 * (1 + 1) ^ (-b)) := h1.2
  have hR3ge : A * 3 * (1 + 3) ^ (-b) ≤ residual A b 3 := h3.1
  have hT1 : powerProfile A b 1 = A * (1 + 1) ^ (-b) := rfl
  have hT3 : powerProfile A b 3 = A * (1 + 3) ^ (-b) := rfl
  rw [div_le_iff₀ hR3pos, hT1, hT3]
  have hexpand : 2 / 3 * (A * (1 + 1) ^ (-b) / (A * (1 + 3) ^ (-b))) * residual A b 3
      = (2 * (A * 1 * (1 + 1) ^ (-b))) * (residual A b 3 / (A * 3 * (1 + 3) ^ (-b))) := by
    field_simp
  rw [hexpand]
  have hratio : 1 ≤ residual A b 3 / (A * 3 * (1 + 3) ^ (-b)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hK : (0:ℝ) ≤ 2 * (A * 1 * (1 + 1) ^ (-b)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hratio hK
  rw [mul_one] at hmul
  exact le_trans hR1le hmul
