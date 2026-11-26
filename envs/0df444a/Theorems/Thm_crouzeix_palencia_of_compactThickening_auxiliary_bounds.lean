-- Prove2me | Theorems.Thm_crouzeix_palencia_of_compactThickening_auxiliary_bounds
-- name    : crouzeix_palencia_of_compactThickening_auxiliary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:59.423998+00:00
-- url     : https://prove2.me/theorems/fc224702-2ab6-4b03-9c32-c99a4b1c59f3
-- title:
--   crouzeix palencia of compact Thickening auxiliary bounds: crouzeix palencia of compact Thickening auxiliary bounds
-- statement:
--   Sharp auxiliary bounds on the canonical compact thickenings of the closed
--   numerical range imply the exact Crouzeix--Palencia conclusion.  The zero
--   Hilbert space is discharged directly; otherwise the closed numerical range
--   is a nonempty compact set, so `compactThickeningApprox_spec` applies.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L145-L184
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L145-L184

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_compactThickening_auxiliary_bounds
    (A : E →L[ℂ] E)
    (haux : ∀ (p : Polynomial ℂ) (n : ℕ), ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ∧
      ‖Polynomial.aeval A p * G‖ ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
