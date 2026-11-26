-- Prove2me | Theorems.Thm_crouzeix_palencia_of_finite_global_bound_of_tendsto_polynomial_companions
-- name    : crouzeix_palencia_of_finite_global_bound_of_tendsto_polynomial_companions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:35:40.827628+00:00
-- url     : https://prove2.me/theorems/0b3b8535-9830-5461-84ae-cc381aae501e
-- title:
--   crouzeix palencia of finite global bound of tendsto polynomial companions: crouzeix palencia of finite global bound of tendsto polynomial companions
-- statement:
--   A finite global polynomial-calculus bound and uniformly contractive
--   polynomial approximants to each auxiliary companion imply the exact
--   Crouzeix--Palencia conclusion.  The operator-norm limit supplies the
--   multiplicative triple estimate, while the preceding best-constant bootstrap
--   globalizes its per-polynomial fourth-power improvement.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L544-L564
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L544-L564

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_finite_global_bound_of_tendsto_polynomial_companions
    (A : E →L[ℂ] E)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A)))
    (hcompanion : ∀ p : Polynomial ℂ,
      ∃ (G : E →L[ℂ] E) (q : ℕ → Polynomial ℂ),
        (∀ n, polynomialSupNorm (q n) (closure (numericalRange A)) ≤
          polynomialSupNorm p (closure (numericalRange A))) ∧
        Filter.Tendsto (fun n ↦ Polynomial.aeval A (q n)) Filter.atTop
          (nhds G) ∧
        ‖Polynomial.aeval A p + star G‖ ≤
          2 * polynomialSupNorm p (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
