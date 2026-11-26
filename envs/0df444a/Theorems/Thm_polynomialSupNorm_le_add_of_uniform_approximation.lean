-- Prove2me | Theorems.Thm_polynomialSupNorm_le_add_of_uniform_approximation
-- name    : polynomialSupNorm_le_add_of_uniform_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:46.089988+00:00
-- url     : https://prove2.me/theorems/c8f5b9fa-c644-57e2-9f99-2e5698c268ff
-- title:
--   polynomial Sup Norm le add of uniform approximation: polynomial Sup Norm le add of uniform approximation
-- statement:
--   If a scalar function is bounded by `m` on `S` and a polynomial uniformly
--   approximates it within `ε`, the polynomial sup norm on `S` is at most
--   `m + ε`.  No compactness assumption is needed because the pointwise upper
--   bound directly controls the conditionally complete supremum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean#L122-L136
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean#L122-L136

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem polynomialSupNorm_le_add_of_uniform_approximation
    (r : Polynomial ℂ) (S : Set ℂ) (g : ℂ → ℂ) (m ε : ℝ)
    (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hg : ∀ z ∈ S, ‖g z‖ ≤ m)
    (happrox : ∀ z ∈ S, ‖Polynomial.eval z r - g z‖ ≤ ε) :
    polynomialSupNorm r S ≤ m + ε := by sorry
