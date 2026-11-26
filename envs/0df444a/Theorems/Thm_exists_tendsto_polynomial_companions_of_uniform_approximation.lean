-- Prove2me | Theorems.Thm_exists_tendsto_polynomial_companions_of_uniform_approximation
-- name    : exists_tendsto_polynomial_companions_of_uniform_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:18.178541+00:00
-- url     : https://prove2.me/theorems/463ba636-aa6c-5885-af16-40f8c6dc0c1f
-- title:
--   exists tendsto polynomial companions of uniform approximation: exists tendsto polynomial companions of uniform approximation
-- statement:
--   Uniform polynomial approximation of a scalar companion bounded by `m`
--   produces an exactly sup-norm-contractive polynomial sequence, provided the
--   polynomial evaluations already converge to the identified operator companion.
--   The latter identification is deliberately separate: analytically it comes
--   from the holomorphic functional calculus for the scalar Cauchy companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean#L143-L159
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean#L143-L159

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_tendsto_polynomial_companions_of_uniform_approximation
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 ≤ m)
    (g : ℂ → ℂ) (hg : ∀ z ∈ S, ‖g z‖ ≤ m)
    (G : E →L[ℂ] E) (hGzero : m = 0 → G = 0)
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ S →
      ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by sorry
