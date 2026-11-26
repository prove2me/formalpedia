-- Prove2me | Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center
-- name    : circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:26.134816+00:00
-- url     : https://prove2.me/theorems/72c0d12e-f9b9-49cb-8b28-627eb1d386b2
-- title:
--   circle Integral resolvent eq two pi I smul one of spectrum subset ball center: circle Integral resolvent eq two pi I smul one of spectrum subset ball center
-- statement:
--   The resolvent mass identity on `C(c, r)` under spectral enclosure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L219-L226
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L219-L226

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball_center
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    circleIntegral (resolvent A) c r = (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
