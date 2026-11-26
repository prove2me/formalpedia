-- Prove2me | Theorems.Thm_circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball
-- name    : circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:39.395827+00:00
-- url     : https://prove2.me/theorems/403298ba-fbb0-5467-b5e0-60ea01aa12de
-- title:
--   circle Integral smul resolvent eq of spectrum subset ball: circle Integral smul resolvent eq of spectrum subset ball
-- statement:
--   Annulus deformation for a scalar-weighted resolvent kernel `g z • R_A z`, where `g` is
--   differentiable off the disk `ball c r` containing the spectrum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L144-L158
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L144-L158

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    {g : ℂ → ℂ} (hg : ∀ z, z ∉ Metric.ball c r → DifferentiableAt ℂ g z) :
    circleIntegral (fun z : ℂ => g z • resolvent A z) c r =
      circleIntegral (fun z : ℂ => g z • resolvent A z) c R := by sorry
