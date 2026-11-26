-- Prove2me | Theorems.Thm_norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt
-- name    : norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:01:18.9078+00:00
-- url     : https://prove2.me/theorems/4d94b829-dd47-5458-a35a-30493fc1e50c
-- title:
--   norm aeval add star le two mul polynomial Sup Norm of representation of norm lt: norm aeval add star le two mul polynomial Sup Norm of representation of norm lt
-- statement:
--   **Circle-model symmetrized Crouzeix–Palencia bound** for `‖A‖ < R`, given the double-layer
--   representation of `p(A) + G†`: `‖p(A) + G†‖ ≤ 2 * sup_{|z| ≤ R} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L131-L141
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L131-L141

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

theorem norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation_of_norm_lt
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : ℂ[X]) (G : E →L[ℂ] E)
    (hrep : aeval A p + star G = (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
      p.eval (circleMap 0 R t) •
        ((-I * deriv (circleMap 0 R) t) • resolvent A (circleMap 0 R t) +
          ContinuousLinearMap.adjoint
            ((-I * deriv (circleMap 0 R) t) • resolvent A (circleMap 0 R t)))) :
    ‖aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by sorry
