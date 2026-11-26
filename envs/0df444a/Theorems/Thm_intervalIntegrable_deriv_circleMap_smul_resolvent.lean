-- Prove2me | Theorems.Thm_intervalIntegrable_deriv_circleMap_smul_resolvent
-- name    : intervalIntegrable_deriv_circleMap_smul_resolvent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:00:50.691021+00:00
-- url     : https://prove2.me/theorems/d8d06d1a-09bb-5675-9072-c1063168f488
-- title:
--   interval Integrable deriv circle Map smul resolvent: interval Integrable deriv circle Map smul resolvent
-- statement:
--   The Cauchy integrand `γ'(t) • R_A(γ(t))` along a circle in the resolvent set is interval
--   integrable over `[0, 2π]`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L65-L72
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L65-L72

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

theorem intervalIntegrable_deriv_circleMap_smul_resolvent (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ => deriv (circleMap c R) t • resolvent A (circleMap c R t))
      MeasureTheory.volume 0 (2 * Real.pi) := by sorry
