-- Prove2me | Theorems.Thm_circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball
-- name    : circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:04.143088+00:00
-- url     : https://prove2.me/theorems/9cdd9912-aacf-45e4-9acc-1830144e3ee9
-- title:
--   circle Integral resolvent eq two pi I smul one of spectrum subset ball: circle Integral resolvent eq two pi I smul one of spectrum subset ball
-- statement:
--   The un-normalized resolvent identity `∮_{|z| = r} R_A(z) dz = 2πi • 1` under spectral
--   enclosure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L111-L117
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L111-L117

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_resolvent_eq_two_pi_I_smul_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) :
    circleIntegral (resolvent A) 0 r = (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
