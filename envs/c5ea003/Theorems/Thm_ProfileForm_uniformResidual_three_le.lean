-- Prove2me | Theorems.Thm_ProfileForm_uniformResidual_three_le
-- name    : ProfileForm.uniformResidual_three_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:38:31.255676+00:00
-- url     : https://prove2.me/theorems/6814b474-b16e-4b4e-a6a0-d76ebcceebe3
-- title:
--   Upper bound at the left end `x = 3`.
-- statement:
--   Upper bound at the left end `x = 3`.
--
--   ```lean
--   theorem ProfileForm.uniformResidual_three_le: uniformResidual 3 ≤ 69/100 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormUniformMixturePeak.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormUniformMixturePeak.lean#L149

-- Thm stub generated from NumberTheory/ProfileFormUniformMixturePeak.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Definitions.Def_NumberTheory_ProfileFormUniformMixturePeak

/-!
# Profile form VII: even the Dickman surrogate humps — outside the window

Second Stage-4 (Critic) result of this cycle, sharper than the two-atom
counterexample of `ProfileFormMixturePeak`.

The mixture-Dickman baseline actually used in the analysis is the *uniform*
scale mixture `M(x) = (1 - e^{-x})/x`.  On the measured window `x ∈ [0,1]` the
residual `T/M` of a power law against it is decreasing, which is why the
observed hump looks like new physics.  But the crossing of the two competing
log-slopes `b/(1+x)` (from the profile) and `1/x - 1/(e^x - 1)` (from the
mixture) happens near `x ≈ 10`, and there the residual really does peak.

We prove this for the measured exponent `b = 11/10`:

`uniformResidual 3 < uniformResidual 10` and `uniformResidual 100 <
uniformResidual 10`,

hence `uniformResidual` attains an interior maximum on `[3, 100]` and is neither
monotone nor antitone there (`uniformResidual_peak`).

Consequence (`peak_is_window_dependent`): *peakedness of the residual is a
window-relative statement*, not an intrinsic property distinguishing the
baseline.  Combined with `ProfileFormResidualPeak.peak_forces_nonPowerLaw_baseline`,
the defensible reading of the experiment is: the measured hump at `x ≈ 0.59`
locates a feature *inside* the analysed window, and its interpretation must be
tied to that window.

The numerical work is done with the rational-exponent trick
`rpow_eleven_tenths_le` / `le_rpow_eleven_tenths`, which converts a bound on
`a ^ (11/10)` into an exact comparison of integer powers.
-/

open ProfileForm

open Set

/-! ## Interior maxima on a general window -/




/-! ## Rational exponents as integer power comparisons -/



/-! ## The residual against the uniform (Dickman surrogate) mixture -/

theorem ProfileForm.uniformResidual_three_le: uniformResidual 3 ≤ 69/100 := by sorry
