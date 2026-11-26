-- Prove2me | Theorems.Thm_intervalIntegral_deriv_circleMap_smul_resolvent_eq
-- name    : intervalIntegral_deriv_circleMap_smul_resolvent_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:48.640467+00:00
-- url     : https://prove2.me/theorems/0646329e-c730-4cef-a41b-c8e16ce73b25
-- title:
--   interval Integral deriv circle Map smul resolvent eq: interval Integral deriv circle Map smul resolvent eq
-- statement:
--   The un-normalized circle Cauchy identity `∫₀^{2π} γ'(t) • R_A(γ(t)) dt = 2πi • 1` for
--   `γ = circleMap 0 R`, `‖A‖ < R`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L117-L127
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L117-L127

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem intervalIntegral_deriv_circleMap_smul_resolvent_eq (A : E →L[ℂ] E) {R : ℝ}
    (hR : ‖A‖ < R) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap 0 R) t • resolvent A (circleMap 0 R t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by sorry
