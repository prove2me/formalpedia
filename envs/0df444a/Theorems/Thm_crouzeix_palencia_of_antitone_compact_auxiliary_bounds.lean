-- Prove2me | Theorems.Thm_crouzeix_palencia_of_antitone_compact_auxiliary_bounds
-- name    : crouzeix_palencia_of_antitone_compact_auxiliary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:49.459322+00:00
-- url     : https://prove2.me/theorems/2fd2167e-8411-41cf-9a2b-6ba496c0bdcf
-- title:
--   crouzeix palencia of antitone compact auxiliary bounds: crouzeix palencia of antitone compact auxiliary bounds
-- statement:
--   If a decreasing sequence of nonempty compact sets intersects to the
--   closed numerical range and the sharp auxiliary bounds hold on every stage,
--   then the exact Crouzeix--Palencia polynomial spectral-set conclusion holds.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L31-L47
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L31-L47

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

theorem crouzeix_palencia_of_antitone_compact_auxiliary_bounds
    (A : E →L[ℂ] E) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (haux : ∀ (p : Polynomial ℂ) (n : ℕ), ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (K n) ∧
      ‖Polynomial.aeval A p * G‖ ≤ polynomialSupNorm p (K n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
