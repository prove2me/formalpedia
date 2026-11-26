-- Prove2me | Theorems.Thm_exists_global_polynomial_calculus_bound_frontier_of_cauchy
-- name    : exists_global_polynomial_calculus_bound_frontier_of_cauchy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:30.756454+00:00
-- url     : https://prove2.me/theorems/d6c726de-8412-4589-8239-6841e12482c9
-- title:
--   exists global polynomial calculus bound frontier of cauchy: exists global polynomial calculus bound frontier of cauchy
-- statement:
--   An all-polynomial Cauchy representation on a fixed smooth domain gives a
--   finite global polynomial-calculus constant relative to the frontier sup norm.
--   The constant is obtained from the compact parameter-interval bound on the
--   unweighted resolvent kernel, extracted by applying the existing auxiliary
--   integrand bound to the constant polynomial `1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L85-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L85-L139

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_global_polynomial_calculus_bound_frontier_of_cauchy
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : ∀ p : Polynomial ℂ, Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z ↦ Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (frontier Omega.carrier) := by sorry
