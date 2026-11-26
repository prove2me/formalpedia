-- Prove2me | Theorems.Thm_crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
-- name    : crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:43.177713+00:00
-- url     : https://prove2.me/theorems/ad5f6020-4994-5b83-a87b-5bb580e9a582
-- title:
--   crouzeix palencia of compact Thickening tendsto polynomial companions: crouzeix palencia of compact Thickening tendsto polynomial companions
-- statement:
--   Finite polynomial-calculus bounds and convergent contractive polynomial
--   companions on every canonical closed thickening imply the exact
--   Crouzeix--Palencia conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L94-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaExhaustion.lean#L94-L139

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

theorem crouzeix_palencia_of_compactThickening_tendsto_polynomial_companions
    (A : E →L[ℂ] E)
    (hfinite : ∀ n, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ C * polynomialSupNorm p
        (compactThickeningApprox (closure (numericalRange A)) n))
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ j, polynomialSupNorm (q j)
            (compactThickeningApprox (closure (numericalRange A)) n) ≤
          polynomialSupNorm p
            (compactThickeningApprox (closure (numericalRange A)) n)) ∧
        Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤ 2 * polynomialSupNorm p
          (compactThickeningApprox (closure (numericalRange A)) n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
