-- Prove2me | Theorems.Thm_exists_bound_crouzeixPolynomialAuxiliaryIntegrand
-- name    : exists_bound_crouzeixPolynomialAuxiliaryIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:35.274221+00:00
-- url     : https://prove2.me/theorems/d9189e06-36ff-57f5-928f-10508bcb7ee7
-- title:
--   exists bound crouzeix Polynomial Auxiliary Integrand: exists bound crouzeix Polynomial Auxiliary Integrand
-- statement:
--   The parameterized conjugate-polynomial resolvent kernel is uniformly
--   bounded on `[0, 2 * pi]`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L117-L149
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L117-L149

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_bound_crouzeixPolynomialAuxiliaryIntegrand [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) •
          resolvent A (Omega.boundaryParam t))‖ ≤ C := by sorry
