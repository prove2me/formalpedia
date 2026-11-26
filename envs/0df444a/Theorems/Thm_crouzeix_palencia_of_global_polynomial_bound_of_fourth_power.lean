-- Prove2me | Theorems.Thm_crouzeix_palencia_of_global_polynomial_bound_of_fourth_power
-- name    : crouzeix_palencia_of_global_polynomial_bound_of_fourth_power
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:35:29.285569+00:00
-- url     : https://prove2.me/theorems/7986bafb-3aee-4be0-bd14-8cfca62a41b3
-- title:
--   crouzeix palencia of global polynomial bound of fourth power: crouzeix palencia of global polynomial bound of fourth power
-- statement:
--   A nonnegative global polynomial-calculus constant satisfying the
--   Ransford--Schwenninger fourth-power inequality is at most `1 + √2`, and hence
--   gives the exact Crouzeix--Palencia polynomial spectral-set conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L371-L384
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L371-L384

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_global_polynomial_bound_of_fourth_power
    (A : E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K)
    (hfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2)
    (hcalc : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
