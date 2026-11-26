-- Prove2me | Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt
-- name    : normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:50.825376+00:00
-- url     : https://prove2.me/theorems/c31ca20b-bd3a-4c1d-ae73-2a635840a693
-- title:
--   normalized circle Integral eval smul resolvent eq aeval of norm sub smul one lt: normalized circle Integral eval smul resolvent eq aeval of norm sub smul one lt
-- statement:
--   The polynomial circle Cauchy formula on `C(c, R)` for `‖A - c • 1‖ < R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L197-L203
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L197-L203

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R = aeval A p := by sorry
