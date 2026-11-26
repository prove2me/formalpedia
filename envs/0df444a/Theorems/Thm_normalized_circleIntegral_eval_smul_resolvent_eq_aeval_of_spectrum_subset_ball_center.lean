-- Prove2me | Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center
-- name    : normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:13.456069+00:00
-- url     : https://prove2.me/theorems/5b497c01-2fa7-4559-93e9-708c08991deb
-- title:
--   normalized circle Integral eval smul resolvent eq aeval of spectrum subset ball center: normalized circle Integral eval smul resolvent eq aeval of spectrum subset ball center
-- statement:
--   The polynomial circle Cauchy formula on `C(c, r)` under spectral enclosure
--   `σ(A) ⊆ ball c r`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L207-L216
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L207-L216

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c r = aeval A p := by sorry
