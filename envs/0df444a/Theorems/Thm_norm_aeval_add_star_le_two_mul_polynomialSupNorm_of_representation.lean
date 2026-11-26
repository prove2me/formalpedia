-- Prove2me | Theorems.Thm_norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation
-- name    : norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:00:56.008964+00:00
-- url     : https://prove2.me/theorems/e88e6806-b42a-535f-b677-27c5ebb00aaa
-- title:
--   norm aeval add star le two mul polynomial Sup Norm of representation: norm aeval add star le two mul polynomial Sup Norm of representation
-- statement:
--   **Circle-model symmetrized Crouzeix–Palencia bound**, given the double-layer representation of
--   `p(A) + G†` and the circle Cauchy identity for the resolvent: if the closure of the numerical range
--   of `A` lies in the open disk `ball c R`, then `‖p(A) + G†‖ ≤ 2 * sup_{|z - c| ≤ R} ‖p(z)‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L77-L101
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/CircleSymmetrized.lean#L77-L101

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

theorem norm_aeval_add_star_le_two_mul_polynomialSupNorm_of_representation (A : E →L[ℂ] E)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hW : closure (numericalRange A) ⊆ Metric.ball c R)
    (p : ℂ[X]) (G : E →L[ℂ] E)
    (hrep : aeval A p + star G = (2 * Real.pi)⁻¹ • ∫ t in (0 : ℝ)..(2 * Real.pi),
      p.eval (circleMap c R t) •
        ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
          ContinuousLinearMap.adjoint
            ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))))
    (hCauchy : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap c R) t • resolvent A (circleMap c R t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E)) :
    ‖aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (Metric.closedBall c R) := by sorry
