-- Prove2me | Theorems.Thm_isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
-- name    : isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:37.986692+00:00
-- url     : https://prove2.me/theorems/e025e105-0131-50f6-91b0-19dd92a38063
-- title:
--   is KPolynomial Spectral Set of finite global bound of tendsto polynomial companions: is KPolynomial Spectral Set of finite global bound of tendsto polynomial companions
-- statement:
--   On a compact control set containing the spectrum, a finite global
--   polynomial-calculus bound and uniformly contractive polynomial approximants
--   to each auxiliary companion imply the `(1 + √2)` spectral-set bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L516-L537
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L516-L537

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem isKPolynomialSpectralSet_of_finite_global_bound_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E) (S : Set ℂ) (hS : IsCompact S)
    (hspectrum : spectrum ℂ A ⊆ S)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p S)
    (hcompanion : ∀ p : Polynomial ℂ,
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ n, polynomialSupNorm (q n) S ≤ polynomialSupNorm p S) ∧
        Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
          (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p S) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) S := by sorry
