-- Prove2me | solution 1 for ProfileForm.not_monotoneOn_of_peak
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:32:12.070514+00:00
-- url     : https://prove2.me/submissions/a8283c2d-619d-460b-92ea-828b76c081ae

-- Sol generated from NumberTheory/ProfileFormResidualPeak.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Definitions.Def_NumberTheory_ProfileFormResidualPeak

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
theorem solution{f : ℝ → ℝ} {c : ℝ} (hc : c ∈ Ioo (0:ℝ) 1)
    (h1 : f 1 < f c) : ¬ MonotoneOn f (Icc (0:ℝ) 1) := by
  intro hmono
  have := hmono (Ioo_subset_Icc_self hc) (right_mem_Icc.mpr zero_le_one) hc.2.le
  linarith
