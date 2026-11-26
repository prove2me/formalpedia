-- Prove2me | Theorems.Thm_circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball
-- name    : circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:23.871706+00:00
-- url     : https://prove2.me/theorems/0051838f-2309-4174-84ee-7aa3c8d30a98
-- title:
--   circle Integral eval smul resolvent eq of spectrum subset ball: circle Integral eval smul resolvent eq of spectrum subset ball
-- statement:
--   **Cauchy deformation for the resolvent kernel.** If the spectrum lies in `ball c r` and
--   `0 < r ≤ R`, the circle integrals of `p(z) • R_A(z)` over `C(c, r)` and `C(c, R)` agree.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L67-L80
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L67-L80

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball (A : E →L[ℂ] E) {c : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hσ : spectrum ℂ A ⊆ Metric.ball c r) (p : ℂ[X]) :
    circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c r =
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R := by sorry
