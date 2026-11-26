-- Prove2me | Theorems.Thm_circleIntegral_eval_smul_resolvent_eq_center
-- name    : circleIntegral_eval_smul_resolvent_eq_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:42.86797+00:00
-- url     : https://prove2.me/theorems/7b91b521-b1fd-56ca-9ea4-cd2daad083ba
-- title:
--   circle Integral eval smul resolvent eq center: circle Integral eval smul resolvent eq center
-- statement:
--   Translating a resolvent circle integral to the centered circle: the integral of
--   `p(z) • R_A(z)` over `C(c, R)` is the integral of `p(w + c) • R_{A - c}(w)` over `C(0, R)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L182-L194
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SpectralCauchy.lean#L182-L194

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem circleIntegral_eval_smul_resolvent_eq_center (A : E →L[ℂ] E) (c : ℂ) (R : ℝ) (p : ℂ[X]) :
    circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R =
      circleIntegral (fun w : ℂ => (p.affineComposition 1 c).eval w •
        resolvent (A - c • (1 : E →L[ℂ] E)) w) 0 R := by sorry
