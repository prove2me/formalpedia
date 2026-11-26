-- Prove2me | Theorems.Thm_polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite
-- name    : polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:52.933031+00:00
-- url     : https://prove2.me/theorems/1b3dd182-d85b-5781-a057-b3ff1d14f2b7
-- title:
--   polynomial auxiliary bounds of normalized of is Compact infinite: polynomial auxiliary bounds of normalized of is Compact infinite
-- statement:
--   On an infinite compact set, sharp auxiliary bounds for all polynomials of
--   sup norm one imply the correctly scaled bounds for every polynomial.  This
--   complements `polynomial_auxiliary_bounds_of_normalized`, whose division
--   argument assumes that the sup norm is positive.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L73-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialSupNormZero.lean#L73-L105

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (hK : IsCompact K) (hKinf : K.Infinite) (p : Polynomial ℂ)
    (hnormalized : ∀ q : Polynomial ℂ,
      polynomialSupNorm q K = 1 →
        ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
          2 * polynomialSupNorm p K ∧
      ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          polynomialSupNorm p K ^ 2 := by sorry
