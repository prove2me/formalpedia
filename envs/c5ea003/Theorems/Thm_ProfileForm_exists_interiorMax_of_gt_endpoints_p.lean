-- Prove2me | Theorems.Thm_ProfileForm_exists_interiorMax_of_gt_endpoints_p
-- name    : ProfileForm.exists_interiorMax_of_gt_endpoints_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:26:01.400987+00:00
-- url     : https://prove2.me/theorems/d5c590a4-b2e7-4713-bc0d-bae87a91c788
-- title:
--   Exists interiorMax of gt endpoints'
-- statement:
--   Formal statement of `ProfileForm.exists_interiorMax_of_gt_endpoints'` from the Aether Catalog (NumberTheory). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ProfileForm.exists_interiorMax_of_gt_endpoints'{f : ℝ → ℝ} {p q c : ℝ} (hpq : p ≤ q)
--       (hf : ContinuousOn f (Icc p q)) (hc : c ∈ Ioo p q)
--       (hp : f p < f c) (hq : f q < f c) :
--       ∃ m ∈ Ioo p q, IsMaxOn f (Icc p q) m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormUniformMixturePeak.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormUniformMixturePeak.lean#L42

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

theorem ProfileForm.exists_interiorMax_of_gt_endpoints_p{f : ℝ → ℝ} {p q c : ℝ} (hpq : p ≤ q)
    (hf : ContinuousOn f (Icc p q)) (hc : c ∈ Ioo p q)
    (hp : f p < f c) (hq : f q < f c) :
    ∃ m ∈ Ioo p q, IsMaxOn f (Icc p q) m := by sorry
