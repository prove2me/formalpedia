-- Prove2me | Theorems.Thm_normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
-- name    : normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:58.847204+00:00
-- url     : https://prove2.me/theorems/44ea4465-a3bc-455c-9453-bb37557a69bd
-- title:
--   normalized circle Integral inv pow smul resolvent eq zero of spectrum subset ball: normalized circle Integral inv pow smul resolvent eq zero of spectrum subset ball
-- statement:
--   Under spectral enclosure `σ(A) ⊆ ball 0 r`, the negative Laurent modes of the resolvent
--   vanish: `(2πi)⁻¹ ∮_{|z| = r} z⁻ⁿ • R_A(z) dz = 0` for `n ≥ 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L162-L176
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L162-L176

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r)
    (n : ℕ) (hn : 0 < n) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 r = 0 := by sorry
