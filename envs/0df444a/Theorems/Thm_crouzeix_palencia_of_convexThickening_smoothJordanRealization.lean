-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_smoothJordanRealization
-- name    : crouzeix_palencia_of_convexThickening_smoothJordanRealization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:39.164494+00:00
-- url     : https://prove2.me/theorems/ec297f7b-a405-40ee-a141-084f1e0cb5b9
-- title:
--   crouzeix palencia of convex Thickening smooth Jordan Realization: crouzeix palencia of convex Thickening smooth Jordan Realization
-- statement:
--   Smooth Jordan realizations of the explicit metric thickenings discharge
--   all analytic inputs to the Crouzeix--Palencia assembly.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean#L36-L45
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean#L36-L45

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_convexThickening_smoothJordanRealization
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
