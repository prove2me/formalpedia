-- Prove2me | Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
-- name    : normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:43.899652+00:00
-- url     : https://prove2.me/theorems/a30078ef-ae33-479d-bb67-19aad12687f4
-- title:
--   normalized circle Integral eval smul resolvent eq aeval of spectrum subset ball: normalized circle Integral eval smul resolvent eq aeval of spectrum subset ball
-- statement:
--   **Circle Cauchy formula under spectral enclosure**: if `σ(A) ⊆ ball 0 r`, then
--   `(2πi)⁻¹ ∮_{|z| = r} p(z) R_A(z) dz = p(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L99-L107
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L99-L107

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r)
    (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) 0 r = aeval A p := by sorry
